import Gdbh.CounterexampleReduction

/-!
# Square-root cofactor sharpening for the counterexample split

This file records a local structural improvement for the two-range
counterexample sieve interface.  Above the square-root barrier, a complement
`m - p` cannot have two distinct prime factors both larger than the threshold
`R`; consequently the cofactor-pair projection used for the large-modulus
covered set is injective.
-/

namespace Gdbh
namespace CounterexampleReduction

/-- Above the square-root barrier, the map from a large-modulus cofactor
witness `(r, k)` to the recovered lower-half prime `m - r * k` is injective.

The only arithmetic input is that two distinct prime moduli `r, s > R`
dividing the same complement would force `(R + 1)^2 ≤ r * s ≤ m`,
contradicting `m < (R + 1)^2`. -/
theorem largeBadLowerHalfPrimeCofactorPairs_image_injOn_of_mul_lt
    {m R : Nat} (hR : m < (R + 1) * (R + 1)) :
    Set.InjOn (fun rk : Nat × Nat => m - rk.1 * rk.2)
      (↑(LargeBadLowerHalfPrimeCofactorPairs m R) : Set (Nat × Nat)) := by
  intro a ha b hb hab
  rcases a with ⟨r, k⟩
  rcases b with ⟨s, l⟩
  have hab' : m - r * k = m - s * l := by
    simpa using hab
  rcases Finset.mem_filter.mp ha with ⟨haprod, hk_two, haplower⟩
  rcases Finset.mem_product.mp haprod with ⟨hrmem, _hk_mem⟩
  rcases Finset.mem_filter.mp hb with ⟨hbprod, hl_two, hblower⟩
  rcases Finset.mem_product.mp hbprod with ⟨hsmem, _hl_mem⟩
  have hrprime : Nat.Prime r :=
    (mem_primeModuliBelow_iff.mp (Finset.mem_filter.mp hrmem).1).1
  have hsprime : Nat.Prime s :=
    (mem_primeModuliBelow_iff.mp (Finset.mem_filter.mp hsmem).1).1
  have hRr : R < r := (Finset.mem_filter.mp hrmem).2
  have hRs : R < s := (Finset.mem_filter.mp hsmem).2
  have hrk_le_m : r * k ≤ m := by
    have hsub_two : 2 ≤ m - r * k :=
      (mem_lowerHalfPrimes_iff.mp haplower).2.two_le
    omega
  have hsl_le_m : s * l ≤ m := by
    have hsub_two : 2 ≤ m - s * l :=
      (mem_lowerHalfPrimes_iff.mp hblower).2.two_le
    omega
  have hprod : r * k = s * l := by
    omega
  have hrs : r = s := by
    by_contra hne
    have hrdvd_sl : r ∣ s * l := by
      rw [← hprod]
      exact dvd_mul_right r k
    have hrdvd_s_or_l : r ∣ s ∨ r ∣ l :=
      (Nat.Prime.dvd_mul hrprime).mp hrdvd_sl
    have hrdvd_l : r ∣ l := by
      rcases hrdvd_s_or_l with hrdvd_s | hrdvd_l
      · have hrs_eq : r = s :=
          (Nat.prime_dvd_prime_iff_eq hrprime hsprime).mp hrdvd_s
        exact False.elim (hne hrs_eq)
      · exact hrdvd_l
    have hr_le_l : r ≤ l := Nat.le_of_dvd (by omega) hrdvd_l
    have hs_le_prod : s * r ≤ s * l := Nat.mul_le_mul_left s hr_le_l
    have hsucc_le_r : R + 1 ≤ r := Nat.succ_le_of_lt hRr
    have hsucc_le_s : R + 1 ≤ s := Nat.succ_le_of_lt hRs
    have hsqr_le_sr : (R + 1) * (R + 1) ≤ s * r :=
      Nat.mul_le_mul hsucc_le_s hsucc_le_r
    have hsr_le_m : s * r ≤ m := le_trans hs_le_prod hsl_le_m
    omega
  subst s
  have hk_eq_l : k = l := by
    exact Nat.mul_left_cancel hrprime.pos hprod
  subst l
  rfl

/-- Cardinality form of the square-root injectivity: above the square-root
barrier the cofactor image has exactly as many points as the cofactor-pair
relation. -/
theorem largeBadLowerHalfPrimeCofactorImage_card_eq_cofactorPairs_card_of_mul_lt
    {m R : Nat} (hR : m < (R + 1) * (R + 1)) :
    (LargeBadLowerHalfPrimeCofactorImage m R).card =
      (LargeBadLowerHalfPrimeCofactorPairs m R).card := by
  unfold LargeBadLowerHalfPrimeCofactorImage
  exact Finset.card_image_of_injOn
    (largeBadLowerHalfPrimeCofactorPairs_image_injOn_of_mul_lt hR)

/-- Above the square-root barrier, the large-modulus covered set and the
cofactor-pair relation have the same cardinality. -/
theorem badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_of_mul_lt
    {m R : Nat} (hR : m < (R + 1) * (R + 1)) :
    (BadLowerHalfPrimesLargeModuli m R).card =
      (LargeBadLowerHalfPrimeCofactorPairs m R).card := by
  rw [← largeBadLowerHalfPrimeCofactorImage_card_eq_largeModuli_card m R]
  exact
    largeBadLowerHalfPrimeCofactorImage_card_eq_cofactorPairs_card_of_mul_lt hR

/-- Under the same square-root condition, the exact split-surplus criterion
implies the cofactor-pair split-surplus criterion; the cofactor-pair count is
not merely an upper bound in this range. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_splitSurplus_of_mul_lt
    {m R : Nat} (hR : m < (R + 1) * (R + 1))
    (hsurplus : LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus m R := by
  unfold LowerHalfPrimeResidueSmallUnionBoundSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus
  rwa [← badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_of_mul_lt hR]

/-- Above the square-root barrier, the exact split-surplus and cofactor-pair
split-surplus local criteria are equivalent. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_of_mul_lt
    {m R : Nat} (hR : m < (R + 1) * (R + 1)) :
    LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m R ↔
      LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus m R :=
  ⟨lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_splitSurplus_of_mul_lt hR,
    lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_of_cofactorSplitSurplus⟩

/-- The natural square-root threshold `Nat.sqrt m ≤ R` implies the
strict square condition used by the cofactor-injectivity lemmas. -/
theorem square_lt_of_sqrt_le {m R : Nat} (hR : Nat.sqrt m ≤ R) :
    m < (R + 1) * (R + 1) := by
  have hsucc : Nat.sqrt m + 1 ≤ R + 1 := Nat.succ_le_succ hR
  have hmul :
      (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤ (R + 1) * (R + 1) :=
    Nat.mul_le_mul hsucc hsucc
  exact lt_of_lt_of_le (Nat.lt_succ_sqrt m) hmul

/-- Natural-threshold form of the cofactor-pair projection injectivity:
choosing `R ≥ sqrt m` puts the large-modulus branch above the square-root
barrier. -/
theorem largeBadLowerHalfPrimeCofactorPairs_image_injOn_of_sqrt_le
    {m R : Nat} (hR : Nat.sqrt m ≤ R) :
    Set.InjOn (fun rk : Nat × Nat => m - rk.1 * rk.2)
      (↑(LargeBadLowerHalfPrimeCofactorPairs m R) : Set (Nat × Nat)) :=
  largeBadLowerHalfPrimeCofactorPairs_image_injOn_of_mul_lt
    (square_lt_of_sqrt_le hR)

/-- Natural-threshold cardinality form for the cofactor image. -/
theorem largeBadLowerHalfPrimeCofactorImage_card_eq_cofactorPairs_card_of_sqrt_le
    {m R : Nat} (hR : Nat.sqrt m ≤ R) :
    (LargeBadLowerHalfPrimeCofactorImage m R).card =
      (LargeBadLowerHalfPrimeCofactorPairs m R).card :=
  largeBadLowerHalfPrimeCofactorImage_card_eq_cofactorPairs_card_of_mul_lt
    (square_lt_of_sqrt_le hR)

/-- Natural-threshold cardinality form for the large-modulus covered set. -/
theorem badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_of_sqrt_le
    {m R : Nat} (hR : Nat.sqrt m ≤ R) :
    (BadLowerHalfPrimesLargeModuli m R).card =
      (LargeBadLowerHalfPrimeCofactorPairs m R).card :=
  badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_of_mul_lt
    (square_lt_of_sqrt_le hR)

/-- With `R ≥ sqrt m`, the exact split-surplus criterion supplies the
cofactor-pair split-surplus criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_splitSurplus_of_sqrt_le
    {m R : Nat} (hR : Nat.sqrt m ≤ R)
    (hsurplus : LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m R) :
    LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus m R :=
  lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_splitSurplus_of_mul_lt
    (square_lt_of_sqrt_le hR) hsurplus

/-- At any threshold `R ≥ sqrt m`, the exact split-surplus and cofactor-pair
split-surplus local criteria are equivalent. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_of_sqrt_le
    {m R : Nat} (hR : Nat.sqrt m ≤ R) :
    LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m R ↔
      LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus m R :=
  lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_of_mul_lt
    (square_lt_of_sqrt_le hR)

/-- Fixed-threshold form at `R = Nat.sqrt m`: the large-modulus covered set
has the same cardinality as the cofactor-pair relation. -/
theorem badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_at_sqrt
    (m : Nat) :
    (BadLowerHalfPrimesLargeModuli m (Nat.sqrt m)).card =
      (LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).card :=
  badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_of_sqrt_le
    (m := m) (R := Nat.sqrt m) le_rfl

/-- At the canonical square-root split, the exact split-surplus and
cofactor-pair split-surplus local criteria are equivalent. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_at_sqrt
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m (Nat.sqrt m) ↔
      LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus
        m (Nat.sqrt m) :=
  lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_of_sqrt_le
    (m := m) (R := Nat.sqrt m) le_rfl

/-- Side-condition-free exact cofactor-cardinality criterion at the
square-root threshold.  This is the fixed-`R` version of the cofactor split
criterion, before any further prime-counting or rectangular-box overcount. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).card <
    (LowerHalfPrimes m).card

/-- The side-condition-free exact square-root cofactor criterion is just the
existing cofactor split criterion specialized to `R = Nat.sqrt m`. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus_iff_cofactorSplitSurplus_at_sqrt
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus m ↔
      LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus
        m (Nat.sqrt m) := by
  rfl

/-- At `R = Nat.sqrt m`, the side-condition-free exact cofactor criterion is
equivalent to the exact split-surplus criterion using the large-modulus
covered set. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus_iff_splitSurplus_at_sqrt
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus m ↔
      LowerHalfPrimeResidueSmallUnionBoundSplitSurplus m (Nat.sqrt m) :=
  (lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus_iff_cofactorSplitSurplus_at_sqrt
    m).trans
    (lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_at_sqrt
      m).symm

/-- Fixed square-root exact-cofactor minimal-counterexample handoff.  A future
proof of this exact cardinality inequality avoids the rectangular-box
prime-counting overcount while still closing the current tail target. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus m

/-- The fixed square-root exact-cofactor handoff supplies the existing
existential-threshold cofactor handoff. -/
theorem minimalCounterexampleFiniteResidueCofactorSplitSurplus_of_sqrtCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus := by
  intro m hm
  exact ⟨Nat.sqrt m,
    (lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus_iff_cofactorSplitSurplus_at_sqrt
      m).mp (hsurplus m hm)⟩

/-- A future proof of the fixed square-root exact-cofactor handoff closes the
literal binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus
    (minimalCounterexampleFiniteResidueCofactorSplitSurplus_of_sqrtCofactorSplitSurplus
      hsurplus)

/-- A future proof of the fixed square-root exact-cofactor handoff closes the
literal remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus
    (minimalCounterexampleFiniteResidueCofactorSplitSurplus_of_sqrtCofactorSplitSurplus
      hsurplus)

/-- The fixed square-root exact-cofactor handoff is exact-strength when stated
over minimal counterexamples.  This records the proof-shape interface without
claiming the needed cardinality inequality. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P := LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus)

/-- The intrinsic cofactor bound at the square-root split is no larger than
`sqrt m`: `m / (sqrt m + 1) ≤ sqrt m`. -/
theorem div_succ_sqrt_le_sqrt (m : Nat) :
    m / (Nat.sqrt m + 1) ≤ Nat.sqrt m := by
  by_contra h
  have hs : Nat.sqrt m + 1 ≤ m / (Nat.sqrt m + 1) :=
    Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
  have hmul :
      (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤
        (m / (Nat.sqrt m + 1)) * (Nat.sqrt m + 1) :=
    Nat.mul_le_mul_right (Nat.sqrt m + 1) hs
  have hdiv :
      (m / (Nat.sqrt m + 1)) * (Nat.sqrt m + 1) ≤ m :=
    Nat.div_mul_le_self m (Nat.sqrt m + 1)
  exact not_lt_of_ge (le_trans hmul hdiv) (Nat.lt_succ_sqrt m)

/-- Fixed square-root rectangular box for large-modulus cofactor witnesses:
`r` is a prime modulus above `sqrt m`, and `2 ≤ k ≤ sqrt m`. -/
def LargeBadLowerHalfPrimeSqrtCofactorBox (m : Nat) :
    Finset (Nat × Nat) :=
  (PrimeModuliBelowAbove m (Nat.sqrt m)).product
    (Finset.Icc 2 (Nat.sqrt m))

/-- At the square-root split, the intrinsically bounded cofactor relation lies
in the simpler `k ≤ sqrt m` box. -/
theorem largeBadLowerHalfPrimeBoundedCofactorPairs_subset_sqrtCofactorBox_at_sqrt
    (m : Nat) :
    LargeBadLowerHalfPrimeBoundedCofactorPairs m (Nat.sqrt m) ⊆
      LargeBadLowerHalfPrimeSqrtCofactorBox m := by
  intro rk hrk
  rcases Finset.mem_filter.mp hrk with ⟨hrkprod, hk_two, _hplower⟩
  rcases Finset.mem_product.mp hrkprod with ⟨hrmem, hk_mem⟩
  have hk_le_div : rk.2 ≤ m / (Nat.sqrt m + 1) :=
    Nat.lt_add_one_iff.mp (Finset.mem_range.mp hk_mem)
  have hk_le_sqrt : rk.2 ≤ Nat.sqrt m :=
    le_trans hk_le_div (div_succ_sqrt_le_sqrt m)
  exact Finset.mem_product.mpr
    ⟨hrmem, Finset.mem_Icc.mpr ⟨hk_two, hk_le_sqrt⟩⟩

/-- The original large-modulus cofactor relation also lies in the fixed
square-root cofactor box. -/
theorem largeBadLowerHalfPrimeCofactorPairs_subset_sqrtCofactorBox_at_sqrt
    (m : Nat) :
    LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m) ⊆
      LargeBadLowerHalfPrimeSqrtCofactorBox m := by
  intro rk hrk
  exact
    largeBadLowerHalfPrimeBoundedCofactorPairs_subset_sqrtCofactorBox_at_sqrt
      m
      (largeBadLowerHalfPrimeCofactorPairs_subset_bounded
        m (Nat.sqrt m) hrk)

/-- Membership in the square-root cofactor relation forces the cofactor
coordinate to satisfy `k ≤ sqrt m`. -/
theorem largeBadLowerHalfPrimeCofactorPairs_snd_le_sqrt_at_sqrt
    {m : Nat} {rk : Nat × Nat}
    (hrk : rk ∈ LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)) :
    rk.2 ≤ Nat.sqrt m := by
  have hbox :
      rk ∈ LargeBadLowerHalfPrimeSqrtCofactorBox m :=
    largeBadLowerHalfPrimeCofactorPairs_subset_sqrtCofactorBox_at_sqrt
      m hrk
  exact (Finset.mem_Icc.mp (Finset.mem_product.mp hbox).2).2

/-- Cardinality of the fixed square-root cofactor box. -/
theorem largeBadLowerHalfPrimeSqrtCofactorBox_card
    (m : Nat) :
    (LargeBadLowerHalfPrimeSqrtCofactorBox m).card =
      (PrimeModuliBelowAbove m (Nat.sqrt m)).card *
        (Finset.Icc 2 (Nat.sqrt m)).card := by
  simp [LargeBadLowerHalfPrimeSqrtCofactorBox]

/-- The exact large-modulus cofactor-pair count is bounded by the fixed
square-root rectangular product. -/
theorem largeBadLowerHalfPrimeCofactorPairs_card_le_sqrtCofactorBoxProduct
    (m : Nat) :
    (LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).card ≤
      (PrimeModuliBelowAbove m (Nat.sqrt m)).card *
        (Finset.Icc 2 (Nat.sqrt m)).card := by
  calc
    (LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).card ≤
        (LargeBadLowerHalfPrimeSqrtCofactorBox m).card :=
      Finset.card_le_card
        (largeBadLowerHalfPrimeCofactorPairs_subset_sqrtCofactorBox_at_sqrt
          m)
    _ =
        (PrimeModuliBelowAbove m (Nat.sqrt m)).card *
          (Finset.Icc 2 (Nat.sqrt m)).card :=
      largeBadLowerHalfPrimeSqrtCofactorBox_card m

/-- Fixed square-root cofactor-pair fiber over a single cofactor value `k`. -/
def LargeBadLowerHalfPrimeSqrtCofactorPairFiber
    (m k : Nat) : Finset (Nat × Nat) :=
  (LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).filter
    fun rk => rk.2 = k

/-- Fixed square-root cofactor fiber over `k`, retaining only the large prime
moduli `r` for which `m - r*k` is a lower-half prime. -/
def LargeBadLowerHalfPrimeSqrtCofactorFiber
    (m k : Nat) : Finset Nat :=
  (PrimeModuliBelowAbove m (Nat.sqrt m)).filter
    fun r => m - r * k ∈ LowerHalfPrimes m

/-- For `2 ≤ k ≤ sqrt m`, the pair fiber is exactly the image of the
one-dimensional modulus fiber under `r ↦ (r,k)`. -/
theorem largeBadLowerHalfPrimeSqrtCofactorPairFiber_eq_fiber_image
    {m k : Nat} (hk : k ∈ Finset.Icc 2 (Nat.sqrt m)) :
    LargeBadLowerHalfPrimeSqrtCofactorPairFiber m k =
      (LargeBadLowerHalfPrimeSqrtCofactorFiber m k).image
        fun r => (r, k) := by
  ext rk
  constructor
  · intro hrk
    rcases Finset.mem_filter.mp hrk with ⟨hrk_pairs, hrk_snd⟩
    rcases Finset.mem_filter.mp hrk_pairs with ⟨hrkprod, _hk_two, hplower⟩
    rcases Finset.mem_product.mp hrkprod with ⟨hrmem, _hk_mem⟩
    refine Finset.mem_image.mpr ⟨rk.1, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hrmem, by simpa [hrk_snd] using hplower⟩
    · ext <;> simp [hrk_snd]
  · intro hrk
    rcases Finset.mem_image.mp hrk with ⟨r, hrfiber, hr_eq⟩
    rcases Finset.mem_filter.mp hrfiber with ⟨hrmem, hplower⟩
    rcases Finset.mem_Icc.mp hk with ⟨hk_two, hk_sqrt⟩
    have hk_le_m : k ≤ m := le_trans hk_sqrt (Nat.sqrt_le_self m)
    have hk_range : k ∈ Finset.range (m + 1) :=
      Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hk_le_m)
    have hpair : (r, k) ∈
        LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hrmem, hk_range⟩, hk_two, hplower⟩
    rw [← hr_eq]
    exact Finset.mem_filter.mpr ⟨hpair, rfl⟩

/-- The pair fiber and the one-dimensional modulus fiber have the same
cardinality. -/
theorem largeBadLowerHalfPrimeSqrtCofactorPairFiber_card_eq_fiber_card
    {m k : Nat} (hk : k ∈ Finset.Icc 2 (Nat.sqrt m)) :
    (LargeBadLowerHalfPrimeSqrtCofactorPairFiber m k).card =
      (LargeBadLowerHalfPrimeSqrtCofactorFiber m k).card := by
  rw [largeBadLowerHalfPrimeSqrtCofactorPairFiber_eq_fiber_image hk]
  exact
    Finset.card_image_of_injOn
      (s := LargeBadLowerHalfPrimeSqrtCofactorFiber m k)
      (f := fun r => (r, k))
      (by
        intro a _ha b _hb hab
        exact (Prod.ext_iff.mp hab).1)

/-- The fixed square-root cofactor-pair count decomposes exactly into pair
fibers over `2 ≤ k ≤ sqrt m`. -/
theorem largeBadLowerHalfPrimeCofactorPairs_card_eq_sum_pairFibers_at_sqrt
    (m : Nat) :
    (LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).card =
      (Finset.Icc 2 (Nat.sqrt m)).sum fun k =>
        (LargeBadLowerHalfPrimeSqrtCofactorPairFiber m k).card := by
  have H : Set.MapsTo (fun rk : Nat × Nat => rk.2)
      (↑(LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)) :
        Set (Nat × Nat))
      (↑(Finset.Icc 2 (Nat.sqrt m)) : Set Nat) := by
    intro rk hrk
    have htwo : 2 ≤ rk.2 := (Finset.mem_filter.mp hrk).2.1
    have hsqrt : rk.2 ≤ Nat.sqrt m :=
      largeBadLowerHalfPrimeCofactorPairs_snd_le_sqrt_at_sqrt hrk
    exact Finset.mem_Icc.mpr ⟨htwo, hsqrt⟩
  simpa [LargeBadLowerHalfPrimeSqrtCofactorPairFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m))
      (t := Finset.Icc 2 (Nat.sqrt m))
      (f := fun rk : Nat × Nat => rk.2) H)

/-- The fixed square-root cofactor-pair count decomposes exactly into
one-dimensional modulus fibers over `2 ≤ k ≤ sqrt m`. -/
theorem largeBadLowerHalfPrimeCofactorPairs_card_eq_sum_fibers_at_sqrt
    (m : Nat) :
    (LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).card =
      (Finset.Icc 2 (Nat.sqrt m)).sum fun k =>
        (LargeBadLowerHalfPrimeSqrtCofactorFiber m k).card := by
  rw [largeBadLowerHalfPrimeCofactorPairs_card_eq_sum_pairFibers_at_sqrt]
  exact
    Finset.sum_congr rfl
      fun k hk =>
        largeBadLowerHalfPrimeSqrtCofactorPairFiber_card_eq_fiber_card hk

/-- Exact square-root cofactor criterion with the large-modulus term written
as a sum of one-dimensional cofactor fibers. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (Finset.Icc 2 (Nat.sqrt m)).sum
        (fun k => (LargeBadLowerHalfPrimeSqrtCofactorFiber m k).card) <
    (LowerHalfPrimes m).card

/-- The fiber-sum criterion is exactly the fixed square-root exact-cofactor
criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus_iff_sqrtCofactorSplitSurplus
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus m ↔
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus
  rw [largeBadLowerHalfPrimeCofactorPairs_card_eq_sum_fibers_at_sqrt]

/-- Minimal-counterexample version of the fixed square-root cofactor
fiber-sum criterion. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus m

/-- The fixed square-root fiber-sum handoff supplies the fixed square-root
exact-cofactor handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_of_sqrtCofactorFiberSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus := by
  intro m hm
  exact
    (lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus_iff_sqrtCofactorSplitSurplus
      m).mp (hsurplus m hm)

/-- A future proof of the fixed square-root fiber-sum handoff closes the
literal binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_of_sqrtCofactorFiberSplitSurplus
      hsurplus)

/-- A future proof of the fixed square-root fiber-sum handoff closes the
literal remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_of_sqrtCofactorFiberSplitSurplus
      hsurplus)

/-- The fixed square-root fiber-sum handoff is exact-strength when stated over
minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorFiberSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P := LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberSplitSurplus)

/-- Lower-half primes in the cofactor residue class modulo `k`.  This is the
one-dimensional target naturally associated to the fixed-`k` cofactor fiber:
if `p = m - r*k`, then `p ≡ m [MOD k]`. -/
def LowerHalfPrimeCofactorResidueClass (m k : Nat) : Finset Nat :=
  (LowerHalfPrimes m).filter fun p => p ≡ m [MOD k]

/-- A cofactor-fiber witness maps into the cofactor residue class modulo
`k`. -/
theorem largeBadLowerHalfPrimeSqrtCofactorFiber_image_subset_cofactorResidueClass
    (m k : Nat) :
    (LargeBadLowerHalfPrimeSqrtCofactorFiber m k).image
        (fun r => m - r * k) ⊆
      LowerHalfPrimeCofactorResidueClass m k := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨r, hrfiber, hp_eq⟩
  rcases Finset.mem_filter.mp hrfiber with ⟨_hrmem, hplower⟩
  have hrk_le : r * k ≤ m := by
    have htwo : 2 ≤ m - r * k :=
      (mem_lowerHalfPrimes_iff.mp hplower).2.two_le
    omega
  have hmod : m - r * k ≡ m [MOD k] := by
    rw [Nat.ModEq]
    have hadd : m - r * k + r * k = m := Nat.sub_add_cancel hrk_le
    nth_rewrite 2 [← hadd]
    simp [Nat.add_mod]
  rw [← hp_eq]
  exact Finset.mem_filter.mpr ⟨hplower, hmod⟩

/-- For `k > 0`, the map `r ↦ m - r*k` is injective on a fixed cofactor
fiber. -/
theorem largeBadLowerHalfPrimeSqrtCofactorFiber_image_injOn
    {m k : Nat} (hk : 0 < k) :
    Set.InjOn (fun r => m - r * k)
      (↑(LargeBadLowerHalfPrimeSqrtCofactorFiber m k) : Set Nat) := by
  intro r hr s hs h
  rcases Finset.mem_filter.mp hr with ⟨_hrmem, hrlower⟩
  rcases Finset.mem_filter.mp hs with ⟨_hsmem, hslower⟩
  have h' : m - r * k = m - s * k := by simpa using h
  have hr_le : r * k ≤ m := by
    have htwo : 2 ≤ m - r * k :=
      (mem_lowerHalfPrimes_iff.mp hrlower).2.two_le
    omega
  have hs_le : s * k ≤ m := by
    have htwo : 2 ≤ m - s * k :=
      (mem_lowerHalfPrimes_iff.mp hslower).2.two_le
    omega
  have hr_add : m - r * k + r * k = m := Nat.sub_add_cancel hr_le
  have hs_add : m - s * k + s * k = m := Nat.sub_add_cancel hs_le
  have hsame : m - s * k + r * k = m - s * k + s * k := by
    calc
      m - s * k + r * k = m - r * k + r * k := by rw [← h']
      _ = m := hr_add
      _ = m - s * k + s * k := hs_add.symm
  have hmul : r * k = s * k := Nat.add_left_cancel hsame
  exact Nat.mul_right_cancel hk hmul

/-- Each fixed-`k` cofactor fiber is bounded by the lower-half prime residue
class modulo `k`. -/
theorem largeBadLowerHalfPrimeSqrtCofactorFiber_card_le_cofactorResidueClass
    {m k : Nat} (hk : 0 < k) :
    (LargeBadLowerHalfPrimeSqrtCofactorFiber m k).card ≤
      (LowerHalfPrimeCofactorResidueClass m k).card := by
  calc
    (LargeBadLowerHalfPrimeSqrtCofactorFiber m k).card =
        ((LargeBadLowerHalfPrimeSqrtCofactorFiber m k).image
          fun r => m - r * k).card := by
      rw [Finset.card_image_of_injOn
        (largeBadLowerHalfPrimeSqrtCofactorFiber_image_injOn
          (m := m) (k := k) hk)]
    _ ≤ (LowerHalfPrimeCofactorResidueClass m k).card :=
      Finset.card_le_card
        (largeBadLowerHalfPrimeSqrtCofactorFiber_image_subset_cofactorResidueClass
          m k)

/-- Summed form: the exact fixed square-root cofactor-pair count is bounded
by the sum of the associated cofactor residue classes modulo
`2 ≤ k ≤ sqrt m`. -/
theorem largeBadLowerHalfPrimeCofactorPairs_card_le_sum_cofactorResidueClasses_at_sqrt
    (m : Nat) :
    (LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).card ≤
      (Finset.Icc 2 (Nat.sqrt m)).sum fun k =>
        (LowerHalfPrimeCofactorResidueClass m k).card := by
  rw [largeBadLowerHalfPrimeCofactorPairs_card_eq_sum_fibers_at_sqrt]
  exact Finset.sum_le_sum fun k hk =>
    largeBadLowerHalfPrimeSqrtCofactorFiber_card_le_cofactorResidueClass
      (m := m) (k := k) (by
        have hk_two : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        omega)

/-- Fixed square-root cofactor-residue criterion.  This replaces the exact
large-modulus cofactor-pair count by a sum of lower-half prime residue classes
modulo the cofactor values `2 ≤ k ≤ sqrt m`. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (Finset.Icc 2 (Nat.sqrt m)).sum
        (fun k => (LowerHalfPrimeCofactorResidueClass m k).card) <
    (LowerHalfPrimes m).card

/-- The fixed square-root cofactor-residue criterion supplies the exact
fiber-sum criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus_of_cofactorResidueSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus
  exact lt_of_le_of_lt
    (Nat.add_le_add_left
      (by
        rw [← largeBadLowerHalfPrimeCofactorPairs_card_eq_sum_fibers_at_sqrt]
        exact
          largeBadLowerHalfPrimeCofactorPairs_card_le_sum_cofactorResidueClasses_at_sqrt
            m)
      (BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m)))
    hsurplus

/-- Minimal-counterexample version of the fixed square-root cofactor-residue
criterion. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus m

/-- The fixed square-root cofactor-residue handoff supplies the fixed
square-root fiber-sum handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorFiberSplitSurplus_of_sqrtCofactorResidueSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus_of_cofactorResidueSplitSurplus
      (hsurplus m hm)

/-- A future proof of the fixed square-root cofactor-residue handoff closes
the literal binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorResidueSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorFiberSplitSurplus_of_sqrtCofactorResidueSplitSurplus
      hsurplus)

/-- A future proof of the fixed square-root cofactor-residue handoff closes
the literal remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorResidueSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorFiberSplitSurplus_of_sqrtCofactorResidueSplitSurplus
      hsurplus)

/-- The fixed square-root cofactor-residue handoff is exact-strength when
stated over minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorResidueSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P := LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorResidueSplitSurplus)

/-- The coprime part of a lower-half cofactor residue class modulo `k`. -/
def LowerHalfPrimeCofactorResidueClassCoprime (m k : Nat) : Finset Nat :=
  (LowerHalfPrimeCofactorResidueClass m k).filter fun p => Nat.Coprime p k

/-- The non-coprime exceptional part of a lower-half cofactor residue class
modulo `k`. -/
def LowerHalfPrimeCofactorResidueClassNoncoprime (m k : Nat) : Finset Nat :=
  (LowerHalfPrimeCofactorResidueClass m k).filter fun p => ¬ Nat.Coprime p k

/-- Lower-half primes dividing `m`; this is the global exceptional set for
non-coprime cofactor residue classes. -/
def LowerHalfPrimeDivisors (m : Nat) : Finset Nat :=
  (LowerHalfPrimes m).filter fun p => p ∣ m

/-- The cofactor residue class splits into coprime and non-coprime parts
relative to the modulus `k`. -/
theorem lowerHalfPrimeCofactorResidueClass_card_eq_coprime_add_noncoprime
    (m k : Nat) :
    (LowerHalfPrimeCofactorResidueClassCoprime m k).card +
        (LowerHalfPrimeCofactorResidueClassNoncoprime m k).card =
      (LowerHalfPrimeCofactorResidueClass m k).card := by
  unfold LowerHalfPrimeCofactorResidueClassCoprime
    LowerHalfPrimeCofactorResidueClassNoncoprime
  simpa using
    (Finset.card_filter_add_card_filter_not
      (s := LowerHalfPrimeCofactorResidueClass m k)
      (p := fun p => Nat.Coprime p k))

/-- Any non-coprime prime in the cofactor residue class modulo `k` must be a
prime divisor of `m`.  Indeed, if `p ∣ k` and `p ≡ m [MOD k]`, reducing the
congruence modulo `p` gives `p ∣ m`. -/
theorem lowerHalfPrimeCofactorResidueClass_noncoprime_subset_lowerHalfPrimeDivisors
    {m k : Nat} :
    LowerHalfPrimeCofactorResidueClassNoncoprime m k ⊆
      LowerHalfPrimeDivisors m := by
  intro p hp
  unfold LowerHalfPrimeCofactorResidueClassNoncoprime at hp
  unfold LowerHalfPrimeDivisors
  rcases Finset.mem_filter.mp hp with ⟨hpclass, hncop⟩
  rcases Finset.mem_filter.mp hpclass with ⟨hplower, hmod⟩
  have hpprime : Nat.Prime p := (mem_lowerHalfPrimes_iff.mp hplower).2
  have hpdvd_k : p ∣ k := hpprime.dvd_iff_not_coprime.mpr hncop
  have hmodp : p ≡ m [MOD p] := hmod.of_dvd hpdvd_k
  have hzero_m : 0 ≡ m [MOD p] :=
    (Nat.modulus_modEq_zero (n := p)).symm.trans hmodp
  have hpdvd_m : p ∣ m := Nat.modEq_zero_iff_dvd.mp hzero_m.symm
  exact Finset.mem_filter.mpr ⟨hplower, hpdvd_m⟩

/-- A cofactor residue class is bounded by its coprime part plus the global
lower-half prime-divisor exceptional set. -/
theorem lowerHalfPrimeCofactorResidueClass_card_le_coprime_add_divisors
    (m k : Nat) :
    (LowerHalfPrimeCofactorResidueClass m k).card ≤
      (LowerHalfPrimeCofactorResidueClassCoprime m k).card +
        (LowerHalfPrimeDivisors m).card := by
  rw [← lowerHalfPrimeCofactorResidueClass_card_eq_coprime_add_noncoprime
    (m := m) (k := k)]
  exact Nat.add_le_add_left
    (Finset.card_le_card
      (lowerHalfPrimeCofactorResidueClass_noncoprime_subset_lowerHalfPrimeDivisors
        (m := m) (k := k)))
    (LowerHalfPrimeCofactorResidueClassCoprime m k).card

/-- Summed coprime-residue form, with one global divisor-error budget repeated
for each cofactor modulus. -/
theorem largeBadLowerHalfPrimeCofactorPairs_card_le_sum_coprimeCofactorResidueClasses_add_divisors_at_sqrt
    (m : Nat) :
    (LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).card ≤
      (Finset.Icc 2 (Nat.sqrt m)).sum fun k =>
        (LowerHalfPrimeCofactorResidueClassCoprime m k).card +
          (LowerHalfPrimeDivisors m).card := by
  exact le_trans
    (largeBadLowerHalfPrimeCofactorPairs_card_le_sum_cofactorResidueClasses_at_sqrt m)
    (Finset.sum_le_sum fun k _hk =>
      lowerHalfPrimeCofactorResidueClass_card_le_coprime_add_divisors
        (m := m) (k := k))

/-- Fixed square-root coprime cofactor-residue criterion.  The large-modulus
side is reduced to coprime residue classes modulo the cofactor values, plus a
global divisor-error term for the non-coprime exceptions. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (Finset.Icc 2 (Nat.sqrt m)).sum
        (fun k =>
          (LowerHalfPrimeCofactorResidueClassCoprime m k).card +
            (LowerHalfPrimeDivisors m).card) <
    (LowerHalfPrimes m).card

/-- The coprime cofactor-residue criterion supplies the cofactor-residue
criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus_of_coprimeResidueSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus
  exact lt_of_le_of_lt
    (Nat.add_le_add_left
      (by
        exact Finset.sum_le_sum fun k _hk =>
          lowerHalfPrimeCofactorResidueClass_card_le_coprime_add_divisors
            (m := m) (k := k))
      (BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m)))
    hsurplus

/-- Minimal-counterexample version of the coprime cofactor-residue criterion. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus m

/-- The coprime cofactor-residue handoff supplies the cofactor-residue handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorResidueSplitSurplus_of_coprimeResidueSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorResidueSplitSurplus_of_coprimeResidueSplitSurplus
      (hsurplus m hm)

/-- A future proof of the coprime cofactor-residue handoff closes the literal
binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResidueSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorResidueSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorResidueSplitSurplus_of_coprimeResidueSplitSurplus
      hsurplus)

/-- A future proof of the coprime cofactor-residue handoff closes the literal
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResidueSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorResidueSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorResidueSplitSurplus_of_coprimeResidueSplitSurplus
      hsurplus)

/-- The coprime cofactor-residue handoff is exact-strength when stated over
minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResidueSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P := LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResidueSplitSurplus)

/-- Lower-half prime divisors of `m` at or below the square-root threshold. -/
def LowerHalfPrimeDivisorsAtMostSqrt (m : Nat) : Finset Nat :=
  (LowerHalfPrimeDivisors m).filter fun p => p ≤ Nat.sqrt m

/-- Lower-half prime divisors of `m` above the square-root threshold. -/
def LowerHalfPrimeDivisorsAboveSqrt (m : Nat) : Finset Nat :=
  (LowerHalfPrimeDivisors m).filter fun p => Nat.sqrt m < p

/-- The lower-half prime divisors split at the square-root threshold. -/
theorem lowerHalfPrimeDivisors_card_eq_atMostSqrt_add_aboveSqrt
    (m : Nat) :
    (LowerHalfPrimeDivisorsAtMostSqrt m).card +
        (LowerHalfPrimeDivisorsAboveSqrt m).card =
      (LowerHalfPrimeDivisors m).card := by
  unfold LowerHalfPrimeDivisorsAtMostSqrt LowerHalfPrimeDivisorsAboveSqrt
  simpa [not_le] using
    (Finset.card_filter_add_card_filter_not
      (s := LowerHalfPrimeDivisors m) (p := fun p => p ≤ Nat.sqrt m))

/-- Small lower-half prime divisors are among the prime moduli below `m` and
at most `sqrt m`. -/
theorem lowerHalfPrimeDivisorsAtMostSqrt_subset_primeModuliBelowAtMost
    (m : Nat) :
    LowerHalfPrimeDivisorsAtMostSqrt m ⊆
      PrimeModuliBelowAtMost m (Nat.sqrt m) := by
  intro p hp
  change p ∈ (LowerHalfPrimeDivisors m).filter
    (fun p => p ≤ Nat.sqrt m) at hp
  rcases Finset.mem_filter.mp hp with ⟨hpdivmem, hpsqrt⟩
  change p ∈ (LowerHalfPrimes m).filter (fun p => p ∣ m) at hpdivmem
  rcases Finset.mem_filter.mp hpdivmem with ⟨hplower, _hpdvd⟩
  rcases mem_lowerHalfPrimes_iff.mp hplower with ⟨hphalf, hpprime⟩
  have hptwo : 2 ≤ p := hpprime.two_le
  exact Finset.mem_filter.mpr
    ⟨mem_primeModuliBelow_iff.mpr ⟨hpprime, by omega⟩, hpsqrt⟩

/-- Cardinal version of the small-divisor inclusion. -/
theorem lowerHalfPrimeDivisorsAtMostSqrt_card_le_primeModuliBelowAtMost
    (m : Nat) :
    (LowerHalfPrimeDivisorsAtMostSqrt m).card ≤
      (PrimeModuliBelowAtMost m (Nat.sqrt m)).card :=
  Finset.card_le_card
    (lowerHalfPrimeDivisorsAtMostSqrt_subset_primeModuliBelowAtMost m)

/-- There is at most one prime divisor of `m` above `sqrt m`. -/
theorem lowerHalfPrimeDivisorsAboveSqrt_card_le_one
    (m : Nat) :
    (LowerHalfPrimeDivisorsAboveSqrt m).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  change p ∈ (LowerHalfPrimeDivisors m).filter
    (fun p => Nat.sqrt m < p) at hp
  change q ∈ (LowerHalfPrimeDivisors m).filter
    (fun p => Nat.sqrt m < p) at hq
  rcases Finset.mem_filter.mp hp with ⟨hpdivmem, hpgt⟩
  rcases Finset.mem_filter.mp hq with ⟨hqdivmem, hqgt⟩
  change p ∈ (LowerHalfPrimes m).filter (fun p => p ∣ m) at hpdivmem
  change q ∈ (LowerHalfPrimes m).filter (fun p => p ∣ m) at hqdivmem
  rcases Finset.mem_filter.mp hpdivmem with ⟨hplower, hpdvd_m⟩
  rcases Finset.mem_filter.mp hqdivmem with ⟨hqlower, hqdvd_m⟩
  have hplower' := mem_lowerHalfPrimes_iff.mp hplower
  have hqlower' := mem_lowerHalfPrimes_iff.mp hqlower
  have hpprime : Nat.Prime p := hplower'.2
  have hqprime : Nat.Prime q := hqlower'.2
  by_contra hpq
  have hpq_dvd_m : p * q ∣ m :=
    Nat.Prime.dvd_mul_of_dvd_ne hpq hpprime hqprime hpdvd_m hqdvd_m
  have hmpos : 0 < m := by omega
  have hpq_le_m : p * q ≤ m := Nat.le_of_dvd hmpos hpq_dvd_m
  have hs_le_p : Nat.sqrt m + 1 ≤ p := Nat.succ_le_iff.mpr hpgt
  have hs_le_q : Nat.sqrt m + 1 ≤ q := Nat.succ_le_iff.mpr hqgt
  have hs_mul_le : (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤ p * q :=
    Nat.mul_le_mul hs_le_p hs_le_q
  have hm_lt_pq : m < p * q :=
    lt_of_lt_of_le (Nat.lt_succ_sqrt m) hs_mul_le
  exact (not_le_of_gt hm_lt_pq) hpq_le_m

/-- The lower-half prime-divisor exceptional set is bounded by the number of
prime moduli up to `sqrt m`, plus one possible prime divisor above `sqrt m`. -/
theorem lowerHalfPrimeDivisors_card_le_primeModuliBelowAtMost_sqrt_add_one
    (m : Nat) :
    (LowerHalfPrimeDivisors m).card ≤
      (PrimeModuliBelowAtMost m (Nat.sqrt m)).card + 1 := by
  rw [← lowerHalfPrimeDivisors_card_eq_atMostSqrt_add_aboveSqrt
    (m := m)]
  exact Nat.add_le_add
    (lowerHalfPrimeDivisorsAtMostSqrt_card_le_primeModuliBelowAtMost m)
    (lowerHalfPrimeDivisorsAboveSqrt_card_le_one m)

/-- For `m > 1`, the divisor-error set is bounded by `π(sqrt m) + 1`. -/
theorem lowerHalfPrimeDivisors_card_le_primeCounting_sqrt_add_one_of_one_lt
    {m : Nat} (hm : 1 < m) :
    (LowerHalfPrimeDivisors m).card ≤
      Nat.primeCounting (Nat.sqrt m) + 1 := by
  calc
    (LowerHalfPrimeDivisors m).card ≤
        (PrimeModuliBelowAtMost m (Nat.sqrt m)).card + 1 :=
      lowerHalfPrimeDivisors_card_le_primeModuliBelowAtMost_sqrt_add_one m
    _ = Nat.primeCounting (Nat.sqrt m) + 1 := by
      rw [primeModuliBelowAtMost_card_eq_primeCounting_of_lt]
      exact Nat.sqrt_lt_self hm

/-- The repeated divisor-error term in the coprime residue-class sum is a
single square-root-length product. -/
theorem cofactorCoprimeResidueClassSum_add_divisors_eq
    (m : Nat) :
    ((Finset.Icc 2 (Nat.sqrt m)).sum fun k =>
        (LowerHalfPrimeCofactorResidueClassCoprime m k).card +
          (LowerHalfPrimeDivisors m).card) =
      ((Finset.Icc 2 (Nat.sqrt m)).sum fun k =>
        (LowerHalfPrimeCofactorResidueClassCoprime m k).card) +
        (Nat.sqrt m - 1) * (LowerHalfPrimeDivisors m).card := by
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_const, Nat.card_Icc]

/-- Fixed square-root coprime cofactor-residue criterion with the divisor
exceptional set replaced by the explicit `π(sqrt m) + 1` bound. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (((Finset.Icc 2 (Nat.sqrt m)).sum fun k =>
        (LowerHalfPrimeCofactorResidueClassCoprime m k).card) +
        (Nat.sqrt m - 1) * (Nat.primeCounting (Nat.sqrt m) + 1)) <
    (LowerHalfPrimes m).card

/-- The `π(sqrt m) + 1` divisor-error criterion supplies the coprime
cofactor-residue criterion for `m > 1`. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus_of_primeCountingDivisorSplitSurplus
    {m : Nat} (hm : 1 < m)
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus
      m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus
  rw [cofactorCoprimeResidueClassSum_add_divisors_eq]
  exact lt_of_le_of_lt
    (Nat.add_le_add_left
      (Nat.add_le_add_left
        (Nat.mul_le_mul_left (Nat.sqrt m - 1)
          (lowerHalfPrimeDivisors_card_le_primeCounting_sqrt_add_one_of_one_lt
            hm))
        ((Finset.Icc 2 (Nat.sqrt m)).sum fun k =>
          (LowerHalfPrimeCofactorResidueClassCoprime m k).card))
      (BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m)))
    hsurplus

/-- Minimal-counterexample version of the `π(sqrt m) + 1` divisor-error
criterion. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus
      m

/-- The `π(sqrt m) + 1` divisor-error handoff supplies the coprime
cofactor-residue handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResidueSplitSurplus_of_primeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResidueSplitSurplus_of_primeCountingDivisorSplitSurplus
      (m := m) (by have hmgt : 50000 < m := hm.2.1; omega)
      (hsurplus m hm)

/-- A future proof of the `π(sqrt m) + 1` divisor-error handoff closes the
literal binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResidueSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResidueSplitSurplus_of_primeCountingDivisorSplitSurplus
      hsurplus)

/-- A future proof of the `π(sqrt m) + 1` divisor-error handoff closes the
literal remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResidueSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResidueSplitSurplus_of_primeCountingDivisorSplitSurplus
      hsurplus)

/-- The `π(sqrt m) + 1` divisor-error handoff is exact-strength when stated
over minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P :=
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus)

/-- Cofactor moduli in the square-root range that are coprime to `m`.  Only
these can contribute to the coprime cofactor-residue classes. -/
def CoprimeCofactorsAtSqrt (m : Nat) : Finset Nat :=
  (Finset.Icc 2 (Nat.sqrt m)).filter fun k => Nat.Coprime m k

/-- If a lower-half prime lies in the coprime cofactor-residue class modulo
`k`, then the modulus `k` is also coprime to `m`. -/
theorem lowerHalfPrimeCofactorResidueClassCoprime_modulus_coprime
    {m p k : Nat}
    (hp : p ∈ LowerHalfPrimeCofactorResidueClassCoprime m k) :
    Nat.Coprime m k := by
  unfold LowerHalfPrimeCofactorResidueClassCoprime at hp
  rcases Finset.mem_filter.mp hp with ⟨hpclass, hpcop⟩
  unfold LowerHalfPrimeCofactorResidueClass at hpclass
  rcases Finset.mem_filter.mp hpclass with ⟨_hplower, hmod⟩
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [← hmod.gcd_eq]
  exact Nat.coprime_iff_gcd_eq_one.mp hpcop

/-- Non-coprime cofactor moduli have empty coprime cofactor-residue class. -/
theorem lowerHalfPrimeCofactorResidueClassCoprime_card_eq_zero_of_not_coprime_modulus
    {m k : Nat} (hnot : ¬ Nat.Coprime m k) :
    (LowerHalfPrimeCofactorResidueClassCoprime m k).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  exact hnot (lowerHalfPrimeCofactorResidueClassCoprime_modulus_coprime hp)

/-- The coprime cofactor-residue sum is supported only on cofactor moduli
`k` with `Nat.Coprime m k`. -/
theorem cofactorCoprimeResidueClassSum_eq_sum_coprimeCofactorsAtSqrt
    (m : Nat) :
    ((Finset.Icc 2 (Nat.sqrt m)).sum fun k =>
        (LowerHalfPrimeCofactorResidueClassCoprime m k).card) =
      (CoprimeCofactorsAtSqrt m).sum fun k =>
        (LowerHalfPrimeCofactorResidueClassCoprime m k).card := by
  symm
  exact Finset.sum_subset (Finset.filter_subset _ _) fun k hkIcc hkNotFilter => by
    have hnot : ¬ Nat.Coprime m k := by
      intro hcop
      exact hkNotFilter (Finset.mem_filter.mpr ⟨hkIcc, hcop⟩)
    exact
      lowerHalfPrimeCofactorResidueClassCoprime_card_eq_zero_of_not_coprime_modulus
        hnot

/-- Fixed square-root coprime cofactor-modulus criterion.  This is the same
prime-counting divisor-error target as above, but the residue-class sum is
restricted to `k` coprime to `m`, because the other coprime residue classes
are empty. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (((CoprimeCofactorsAtSqrt m).sum fun k =>
        (LowerHalfPrimeCofactorResidueClassCoprime m k).card) +
        (Nat.sqrt m - 1) * (Nat.primeCounting (Nat.sqrt m) + 1)) <
    (LowerHalfPrimes m).card

/-- The coprime-modulus criterion supplies the prime-counting divisor-error
criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus_of_coprimeModulusPrimeCountingDivisorSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus
      m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus at hsurplus
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus
  rwa [cofactorCoprimeResidueClassSum_eq_sum_coprimeCofactorsAtSqrt]

/-- Minimal-counterexample version of the coprime-modulus prime-counting
divisor-error criterion. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus
      m

/-- The coprime-modulus handoff supplies the prime-counting divisor-error
handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus_of_coprimeModulusPrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus_of_coprimeModulusPrimeCountingDivisorSplitSurplus
      (hsurplus m hm)

/-- A future proof of the coprime-modulus handoff closes the literal binary
Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus_of_coprimeModulusPrimeCountingDivisorSplitSurplus
      hsurplus)

/-- A future proof of the coprime-modulus handoff closes the literal
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus_of_coprimeModulusPrimeCountingDivisorSplitSurplus
      hsurplus)

/-- The coprime-modulus handoff is exact-strength when stated over minimal
counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P :=
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus)

/-- On a cofactor modulus coprime to `m`, every lower-half prime in the
residue class `p ≡ m [MOD k]` is automatically coprime to `k`. -/
theorem lowerHalfPrimeCofactorResidueClass_coprime_of_modulus_coprime
    {m p k : Nat} (hcop : Nat.Coprime m k)
    (hp : p ∈ LowerHalfPrimeCofactorResidueClass m k) :
    Nat.Coprime p k := by
  unfold LowerHalfPrimeCofactorResidueClass at hp
  rcases Finset.mem_filter.mp hp with ⟨_hplower, hmod⟩
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [hmod.gcd_eq]
  exact Nat.coprime_iff_gcd_eq_one.mp hcop

/-- For a cofactor modulus coprime to `m`, the explicit `p`-coprime filter
on the residue class is redundant. -/
theorem lowerHalfPrimeCofactorResidueClassCoprime_eq_of_modulus_coprime
    {m k : Nat} (hcop : Nat.Coprime m k) :
    LowerHalfPrimeCofactorResidueClassCoprime m k =
      LowerHalfPrimeCofactorResidueClass m k := by
  unfold LowerHalfPrimeCofactorResidueClassCoprime
  ext p
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).1
  · intro hp
    exact Finset.mem_filter.mpr
      ⟨hp, lowerHalfPrimeCofactorResidueClass_coprime_of_modulus_coprime
        hcop hp⟩

/-- After restricting to cofactor moduli coprime to `m`, the coprime
cofactor-residue sum is the unfiltered primitive residue-class sum. -/
theorem cofactorCoprimeResidueClassSum_coprimeCofactorsAtSqrt_eq_unfiltered
    (m : Nat) :
    ((CoprimeCofactorsAtSqrt m).sum fun k =>
        (LowerHalfPrimeCofactorResidueClassCoprime m k).card) =
      (CoprimeCofactorsAtSqrt m).sum fun k =>
        (LowerHalfPrimeCofactorResidueClass m k).card := by
  exact Finset.sum_congr rfl fun k hk => by
    have hcop : Nat.Coprime m k := (Finset.mem_filter.mp hk).2
    rw [lowerHalfPrimeCofactorResidueClassCoprime_eq_of_modulus_coprime
      hcop]

/-- The original square-root coprime-residue sum can be rewritten as a
primitive residue-class sum over cofactor moduli coprime to `m`. -/
theorem cofactorCoprimeResidueClassSum_eq_sum_coprimeCofactorsAtSqrt_unfiltered
    (m : Nat) :
    ((Finset.Icc 2 (Nat.sqrt m)).sum fun k =>
        (LowerHalfPrimeCofactorResidueClassCoprime m k).card) =
      (CoprimeCofactorsAtSqrt m).sum fun k =>
        (LowerHalfPrimeCofactorResidueClass m k).card := by
  rw [cofactorCoprimeResidueClassSum_eq_sum_coprimeCofactorsAtSqrt]
  exact cofactorCoprimeResidueClassSum_coprimeCofactorsAtSqrt_eq_unfiltered m

/-- Fixed square-root primitive residue-class criterion.  The cofactor
moduli are restricted to `Nat.Coprime m k`, and the summand is the ordinary
lower-half residue class `p ≡ m [MOD k]`; the primitive condition makes the
extra `Nat.Coprime p k` filter redundant. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (((CoprimeCofactorsAtSqrt m).sum fun k =>
        (LowerHalfPrimeCofactorResidueClass m k).card) +
        (Nat.sqrt m - 1) * (Nat.primeCounting (Nat.sqrt m) + 1)) <
    (LowerHalfPrimes m).card

/-- The primitive residue-class criterion supplies the coprime-modulus
prime-counting divisor-error criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus_of_primitiveResiduePrimeCountingDivisorSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus
      m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus at hsurplus
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus
  rwa [cofactorCoprimeResidueClassSum_coprimeCofactorsAtSqrt_eq_unfiltered]

/-- Minimal-counterexample version of the primitive residue-class
prime-counting divisor-error criterion. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus
      m

/-- The primitive residue-class handoff supplies the coprime-modulus handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus_of_primitiveResiduePrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus_of_primitiveResiduePrimeCountingDivisorSplitSurplus
      (hsurplus m hm)

/-- A future proof of the primitive residue-class handoff closes the literal
binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus_of_primitiveResiduePrimeCountingDivisorSplitSurplus
      hsurplus)

/-- A future proof of the primitive residue-class handoff closes the literal
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus_of_primitiveResiduePrimeCountingDivisorSplitSurplus
      hsurplus)

/-- The primitive residue-class handoff is exact-strength when stated over
minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P :=
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus)

/-- Primes up to `N` in the residue class `a` modulo `q`.  This is the
standard AP-counting form of the cofactor residue classes. -/
def PrimeResidueClassUpTo (N a q : Nat) : Finset Nat :=
  (Finset.range (N + 1)).filter fun p => Nat.Prime p ∧ p ≡ a [MOD q]

/-- The lower-half cofactor residue class is exactly the AP prime-counting
set up to `m / 2`. -/
theorem lowerHalfPrimeCofactorResidueClass_eq_primeResidueClassUpTo_half
    (m k : Nat) :
    LowerHalfPrimeCofactorResidueClass m k =
      PrimeResidueClassUpTo (m / 2) m k := by
  unfold LowerHalfPrimeCofactorResidueClass LowerHalfPrimes
    PrimeResidueClassUpTo
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hplower, hmod⟩
    rcases Finset.mem_filter.mp hplower with ⟨hrange, hprime⟩
    exact Finset.mem_filter.mpr ⟨hrange, hprime, hmod⟩
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hrange, hprime, hmod⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hrange, hprime⟩, hmod⟩

/-- Summed form of the AP-counting rewrite for primitive cofactor moduli. -/
theorem cofactorPrimitiveResidueClassSum_eq_primeResidueClassUpTo_half
    (m : Nat) :
    ((CoprimeCofactorsAtSqrt m).sum fun k =>
        (LowerHalfPrimeCofactorResidueClass m k).card) =
      (CoprimeCofactorsAtSqrt m).sum fun k =>
        (PrimeResidueClassUpTo (m / 2) m k).card := by
  exact Finset.sum_congr rfl fun k _hk => by
    rw [lowerHalfPrimeCofactorResidueClass_eq_primeResidueClassUpTo_half]

/-- Fixed square-root AP residue-class criterion.  This is the primitive
residue-class handoff rewritten with the explicit AP counting set
`PrimeResidueClassUpTo`. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (((CoprimeCofactorsAtSqrt m).sum fun k =>
        (PrimeResidueClassUpTo (m / 2) m k).card) +
        (Nat.sqrt m - 1) * (Nat.primeCounting (Nat.sqrt m) + 1)) <
    (LowerHalfPrimes m).card

/-- The AP residue-class criterion supplies the primitive residue-class
criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus_of_apResiduePrimeCountingDivisorSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus
      m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus at hsurplus
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus
  rwa [cofactorPrimitiveResidueClassSum_eq_primeResidueClassUpTo_half]

/-- Minimal-counterexample version of the AP residue-class criterion. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus
      m

/-- The AP residue-class handoff supplies the primitive residue-class
handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus_of_apResiduePrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus_of_apResiduePrimeCountingDivisorSplitSurplus
      (hsurplus m hm)

/-- A future proof of the AP residue-class handoff closes the literal binary
Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus_of_apResiduePrimeCountingDivisorSplitSurplus
      hsurplus)

/-- A future proof of the AP residue-class handoff closes the literal
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus_of_apResiduePrimeCountingDivisorSplitSurplus
      hsurplus)

/-- The AP residue-class handoff is exact-strength when stated over minimal
counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P :=
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus)

/-- AP residue-class criterion with the right side written in the standard
prime-counting form.  This is only a normalization of
`LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus`;
the analytic content remains the AP residue-class sum plus the explicit
square-root divisor-error term. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (((CoprimeCofactorsAtSqrt m).sum fun k =>
        (PrimeResidueClassUpTo (m / 2) m k).card) +
        (Nat.sqrt m - 1) * (Nat.primeCounting (Nat.sqrt m) + 1)) <
    Nat.primeCounting (m / 2)

/-- The AP residue-class divisor-error criterion is equivalent to its
standard prime-counting right-side normalization. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus_iff_apResiduePrimeCountingDivisorFullSplitSurplus
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus
        m ↔
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
        m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
  rw [lowerHalfPrimes_card_eq_primeCounting_half]

/-- The prime-counting right-side AP criterion supplies the previous AP
residue-class criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus_of_apResiduePrimeCountingDivisorFullSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus
      m :=
  (lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus_iff_apResiduePrimeCountingDivisorFullSplitSurplus
    m).mpr hsurplus

/-- Minimal-counterexample version of the AP criterion with a standard
prime-counting right side. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
      m

/-- The prime-counting right-side AP handoff supplies the previous AP
residue-class handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus_of_apResiduePrimeCountingDivisorFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus_of_apResiduePrimeCountingDivisorFullSplitSurplus
      (hsurplus m hm)

/-- A future proof of the prime-counting right-side AP handoff closes the
literal binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus_of_apResiduePrimeCountingDivisorFullSplitSurplus
      hsurplus)

/-- A future proof of the prime-counting right-side AP handoff closes the
literal remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus_of_apResiduePrimeCountingDivisorFullSplitSurplus
      hsurplus)

/-- The prime-counting right-side AP handoff is exact-strength when stated
over minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P :=
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus)

/-- A named budget for the small-residue contribution at the square-root
threshold. -/
def LowerHalfPrimeSmallResidueClassSqrtBudget
    (m budget : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) ≤ budget

/-- A named budgeted AP remainder target: after reserving `budget` for the
small-residue term, the AP residue-class sum plus divisor-error term still
stays below `π(m / 2)`. -/
def SqrtCofactorAPResiduePrimeCountingDivisorRemainderBudget
    (m budget : Nat) : Prop :=
  budget +
      (((CoprimeCofactorsAtSqrt m).sum fun k =>
        (PrimeResidueClassUpTo (m / 2) m k).card) +
        (Nat.sqrt m - 1) * (Nat.primeCounting (Nat.sqrt m) + 1)) <
    Nat.primeCounting (m / 2)

/-- Budget-split form of the AP full-RHS criterion.  It separates the
small-residue contribution from the AP residue-class and divisor-error
remainder. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
    (m budget : Nat) : Prop :=
  LowerHalfPrimeSmallResidueClassSqrtBudget m budget ∧
    SqrtCofactorAPResiduePrimeCountingDivisorRemainderBudget m budget

/-- The budget split supplies the AP full-RHS criterion by adding the two
budget inequalities. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus_of_budgetSplitSurplus
    {m budget : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
        m budget) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
      m := by
  rcases hsurplus with ⟨hsmall, hremainder⟩
  unfold LowerHalfPrimeSmallResidueClassSqrtBudget at hsmall
  unfold SqrtCofactorAPResiduePrimeCountingDivisorRemainderBudget at hremainder
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
  omega

/-- Minimal-counterexample version of the budget-split AP criterion.  The
budget may depend on `m`; future analytic work can choose a concrete budget
function and prove the two named sub-inequalities separately. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
    (budget : Nat → Nat) : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
      m (budget m)

/-- The budget-split handoff supplies the AP full-RHS handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus_of_budgetSplitSurplus
    (budget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
        budget) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus_of_budgetSplitSurplus
      (hsurplus m hm)

/-- A future proof of the budget-split AP handoff closes the literal binary
Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
    (budget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
        budget) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus_of_budgetSplitSurplus
      budget hsurplus)

/-- A future proof of the budget-split AP handoff closes the literal
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
    (budget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
        budget) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus_of_budgetSplitSurplus
      budget hsurplus)

/-- For any fixed budget function, the budget-split AP handoff is
exact-strength when stated over minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus_iff_explicitLowerBound50000
    (budget : Nat → Nat) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
        budget ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P := fun m =>
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
          m (budget m))
      (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
        budget))

/-- A named budget for the primitive cofactor AP residue-class sum. -/
def SqrtCofactorAPResidueClassSumBudget
    (m apBudget : Nat) : Prop :=
  ((CoprimeCofactorsAtSqrt m).sum fun k =>
    (PrimeResidueClassUpTo (m / 2) m k).card) ≤ apBudget

/-- A named budget for the square-root divisor-error term. -/
def SqrtCofactorPrimeCountingDivisorErrorBudget
    (m divisorBudget : Nat) : Prop :=
  (Nat.sqrt m - 1) * (Nat.primeCounting (Nat.sqrt m) + 1) ≤
    divisorBudget

/-- The pure arithmetic margin left after assigning budgets to the three
pieces of the AP full-RHS criterion. -/
def SqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetMargin
    (m smallBudget apBudget divisorBudget : Nat) : Prop :=
  smallBudget + (apBudget + divisorBudget) < Nat.primeCounting (m / 2)

/-- Three-budget form of the AP full-RHS criterion.  It separates the small
residue-class term, the primitive cofactor AP sum, and the divisor-error
term. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
    (m smallBudget apBudget divisorBudget : Nat) : Prop :=
  LowerHalfPrimeSmallResidueClassSqrtBudget m smallBudget ∧
    SqrtCofactorAPResidueClassSumBudget m apBudget ∧
    SqrtCofactorPrimeCountingDivisorErrorBudget m divisorBudget ∧
    SqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetMargin
      m smallBudget apBudget divisorBudget

/-- The three-budget split supplies the earlier one-budget split by adding
the AP-sum and divisor-error budgets inside the remaining margin. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus_of_threeBudgetSplitSurplus
    {m smallBudget apBudget divisorBudget : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
        m smallBudget apBudget divisorBudget) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
      m smallBudget := by
  rcases hsurplus with ⟨hsmall, hap, hdivisor, hmargin⟩
  refine ⟨hsmall, ?_⟩
  unfold SqrtCofactorAPResiduePrimeCountingDivisorRemainderBudget
  unfold SqrtCofactorAPResidueClassSumBudget at hap
  unfold SqrtCofactorPrimeCountingDivisorErrorBudget at hdivisor
  unfold SqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetMargin at hmargin
  omega

/-- Minimal-counterexample version of the three-budget AP criterion. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
    (smallBudget apBudget divisorBudget : Nat → Nat) : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
      m (smallBudget m) (apBudget m) (divisorBudget m)

/-- The three-budget handoff supplies the one-budget handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus_of_threeBudgetSplitSurplus
    (smallBudget apBudget divisorBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
        smallBudget apBudget divisorBudget) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
      smallBudget := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus_of_threeBudgetSplitSurplus
      (hsurplus m hm)

/-- A future proof of the three-budget AP handoff closes the literal binary
Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
    (smallBudget apBudget divisorBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
        smallBudget apBudget divisorBudget) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
    smallBudget
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus_of_threeBudgetSplitSurplus
      smallBudget apBudget divisorBudget hsurplus)

/-- A future proof of the three-budget AP handoff closes the literal
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
    (smallBudget apBudget divisorBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
        smallBudget apBudget divisorBudget) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus
    smallBudget
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus_of_threeBudgetSplitSurplus
      smallBudget apBudget divisorBudget hsurplus)

/-- For any chosen three budget functions, the three-budget AP handoff is
exact-strength when stated over minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus_iff_explicitLowerBound50000
    (smallBudget apBudget divisorBudget : Nat → Nat) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
        smallBudget apBudget divisorBudget ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P := fun m =>
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
          m (smallBudget m) (apBudget m) (divisorBudget m))
      (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
        smallBudget apBudget divisorBudget))

/-- Pointwise budgets for each primitive cofactor AP residue class. -/
def SqrtCofactorAPResidueClassPointwiseBudget
    (m : Nat) (pointBudget : Nat → Nat) : Prop :=
  ∀ k ∈ CoprimeCofactorsAtSqrt m,
    (PrimeResidueClassUpTo (m / 2) m k).card ≤ pointBudget k

/-- A summed budget for the pointwise primitive cofactor AP residue-class
budgets. -/
def SqrtCofactorAPResidueClassPointwiseBudgetSum
    (m : Nat) (pointBudget : Nat → Nat) (apBudget : Nat) : Prop :=
  ((CoprimeCofactorsAtSqrt m).sum fun k => pointBudget k) ≤ apBudget

/-- Pointwise AP residue-class budgets supply the aggregate AP-sum budget. -/
theorem sqrtCofactorAPResidueClassSumBudget_of_pointwiseBudget
    {m apBudget : Nat} {pointBudget : Nat → Nat}
    (hpoint : SqrtCofactorAPResidueClassPointwiseBudget m pointBudget)
    (hsum :
      SqrtCofactorAPResidueClassPointwiseBudgetSum
        m pointBudget apBudget) :
    SqrtCofactorAPResidueClassSumBudget m apBudget := by
  unfold SqrtCofactorAPResidueClassSumBudget
  unfold SqrtCofactorAPResidueClassPointwiseBudget at hpoint
  unfold SqrtCofactorAPResidueClassPointwiseBudgetSum at hsum
  exact le_trans (Finset.sum_le_sum fun k hk => hpoint k hk) hsum

/-- Three-budget AP split with the AP-sum budget itself decomposed into
pointwise residue-class budgets over primitive cofactor moduli. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
    (m smallBudget apBudget divisorBudget : Nat)
    (pointBudget : Nat → Nat) : Prop :=
  LowerHalfPrimeSmallResidueClassSqrtBudget m smallBudget ∧
    SqrtCofactorAPResidueClassPointwiseBudget m pointBudget ∧
    SqrtCofactorAPResidueClassPointwiseBudgetSum m pointBudget apBudget ∧
    SqrtCofactorPrimeCountingDivisorErrorBudget m divisorBudget ∧
    SqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetMargin
      m smallBudget apBudget divisorBudget

/-- The pointwise AP budget split supplies the three-budget split. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus_of_pointwiseAPBudgetSplitSurplus
    {m smallBudget apBudget divisorBudget : Nat}
    {pointBudget : Nat → Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
        m smallBudget apBudget divisorBudget pointBudget) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
      m smallBudget apBudget divisorBudget := by
  rcases hsurplus with ⟨hsmall, hpoint, hsum, hdivisor, hmargin⟩
  exact ⟨hsmall,
    sqrtCofactorAPResidueClassSumBudget_of_pointwiseBudget hpoint hsum,
    hdivisor, hmargin⟩

/-- Minimal-counterexample version of the pointwise AP budget split.  The
pointwise AP budget may depend on both the candidate counterexample `m` and
the cofactor modulus `k`. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
    (smallBudget apBudget divisorBudget : Nat → Nat)
    (pointBudget : Nat → Nat → Nat) : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
      m (smallBudget m) (apBudget m) (divisorBudget m) (pointBudget m)

/-- The pointwise AP budget handoff supplies the three-budget handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus_of_pointwiseAPBudgetSplitSurplus
    (smallBudget apBudget divisorBudget : Nat → Nat)
    (pointBudget : Nat → Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
        smallBudget apBudget divisorBudget pointBudget) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
      smallBudget apBudget divisorBudget := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus_of_pointwiseAPBudgetSplitSurplus
      (hsurplus m hm)

/-- A future proof of the pointwise AP budget handoff closes the literal
binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
    (smallBudget apBudget divisorBudget : Nat → Nat)
    (pointBudget : Nat → Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
        smallBudget apBudget divisorBudget pointBudget) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
    smallBudget apBudget divisorBudget
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus_of_pointwiseAPBudgetSplitSurplus
      smallBudget apBudget divisorBudget pointBudget hsurplus)

/-- A future proof of the pointwise AP budget handoff closes the literal
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
    (smallBudget apBudget divisorBudget : Nat → Nat)
    (pointBudget : Nat → Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
        smallBudget apBudget divisorBudget pointBudget) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus
    smallBudget apBudget divisorBudget
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus_of_pointwiseAPBudgetSplitSurplus
      smallBudget apBudget divisorBudget pointBudget hsurplus)

/-- For any chosen budget functions, the pointwise AP budget handoff is
exact-strength when stated over minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus_iff_explicitLowerBound50000
    (smallBudget apBudget divisorBudget : Nat → Nat)
    (pointBudget : Nat → Nat → Nat) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
        smallBudget apBudget divisorBudget pointBudget ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P := fun m =>
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
          m (smallBudget m) (apBudget m) (divisorBudget m) (pointBudget m))
      (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
        smallBudget apBudget divisorBudget pointBudget))

/-- AP primes in one residue class are bounded by the elementary point count
for that residue class. -/
theorem primeResidueClassUpTo_card_le_pointBound
    (N a q : Nat) :
    (PrimeResidueClassUpTo N a q).card ≤ N / q + 1 := by
  have hsubset :
      PrimeResidueClassUpTo N a q ⊆
        (Finset.range (N + 1)).filter (fun p => p % q = a % q) := by
    intro p hp
    unfold PrimeResidueClassUpTo at hp
    rcases Finset.mem_filter.mp hp with ⟨hrange, _hprime, hmod⟩
    exact Finset.mem_filter.mpr
      ⟨hrange, by simpa [Nat.ModEq] using hmod⟩
  exact le_trans (Finset.card_le_card hsubset)
    (card_filter_range_modEq_le_div_add_one N a q)

/-- Elementary pointwise budget for one primitive cofactor AP residue class. -/
def SqrtCofactorAPResidueClassElementaryPointBudget
    (m k : Nat) : Nat :=
  (m / 2) / k + 1

/-- The elementary point count supplies every primitive cofactor AP
residue-class pointwise budget. -/
theorem sqrtCofactorAPResidueClassPointwiseBudget_elementaryPointBudget
    (m : Nat) :
    SqrtCofactorAPResidueClassPointwiseBudget m
      (SqrtCofactorAPResidueClassElementaryPointBudget m) := by
  intro k _hk
  unfold SqrtCofactorAPResidueClassElementaryPointBudget
  exact primeResidueClassUpTo_card_le_pointBound (m / 2) m k

/-- Summed elementary pointwise AP budget over primitive cofactor moduli. -/
def SqrtCofactorAPResidueClassElementaryPointBudgetSum
    (m : Nat) : Nat :=
  (CoprimeCofactorsAtSqrt m).sum fun k =>
    SqrtCofactorAPResidueClassElementaryPointBudget m k

/-- The summed elementary AP point budget is a valid aggregate pointwise
budget. -/
theorem sqrtCofactorAPResidueClassPointwiseBudgetSum_elementaryPointBudget
    (m : Nat) :
    SqrtCofactorAPResidueClassPointwiseBudgetSum m
      (SqrtCofactorAPResidueClassElementaryPointBudget m)
      (SqrtCofactorAPResidueClassElementaryPointBudgetSum m) := by
  unfold SqrtCofactorAPResidueClassPointwiseBudgetSum
  unfold SqrtCofactorAPResidueClassElementaryPointBudgetSum
  exact le_rfl

/-- Pointwise AP split after replacing AP residue-class estimates by the
elementary point-count budget `m / 2 / k + 1`. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
    (m smallBudget divisorBudget : Nat) : Prop :=
  LowerHalfPrimeSmallResidueClassSqrtBudget m smallBudget ∧
    SqrtCofactorPrimeCountingDivisorErrorBudget m divisorBudget ∧
    SqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetMargin
      m smallBudget (SqrtCofactorAPResidueClassElementaryPointBudgetSum m)
      divisorBudget

/-- The elementary point-count AP split supplies the pointwise AP-budget
handoff. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus_of_elementaryPointAPSplitSurplus
    {m smallBudget divisorBudget : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
        m smallBudget divisorBudget) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
      m smallBudget (SqrtCofactorAPResidueClassElementaryPointBudgetSum m)
      divisorBudget (SqrtCofactorAPResidueClassElementaryPointBudget m) := by
  rcases hsurplus with ⟨hsmall, hdivisor, hmargin⟩
  exact ⟨hsmall,
    sqrtCofactorAPResidueClassPointwiseBudget_elementaryPointBudget m,
    sqrtCofactorAPResidueClassPointwiseBudgetSum_elementaryPointBudget m,
    hdivisor, hmargin⟩

/-- Minimal-counterexample version of the elementary point-count AP split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
    (smallBudget divisorBudget : Nat → Nat) : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
      m (smallBudget m) (divisorBudget m)

/-- The elementary point-count AP split supplies the pointwise AP-budget
minimal-counterexample handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus_of_elementaryPointAPSplitSurplus
    (smallBudget divisorBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
        smallBudget divisorBudget) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
      smallBudget
      (fun m => SqrtCofactorAPResidueClassElementaryPointBudgetSum m)
      divisorBudget
      (fun m => SqrtCofactorAPResidueClassElementaryPointBudget m) := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus_of_elementaryPointAPSplitSurplus
      (hsurplus m hm)

/-- A future proof of the elementary point-count AP split closes the literal
binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
    (smallBudget divisorBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
        smallBudget divisorBudget) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
    smallBudget
    (fun m => SqrtCofactorAPResidueClassElementaryPointBudgetSum m)
    divisorBudget
    (fun m => SqrtCofactorAPResidueClassElementaryPointBudget m)
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus_of_elementaryPointAPSplitSurplus
      smallBudget divisorBudget hsurplus)

/-- A future proof of the elementary point-count AP split closes the literal
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
    (smallBudget divisorBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
        smallBudget divisorBudget) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus
    smallBudget
    (fun m => SqrtCofactorAPResidueClassElementaryPointBudgetSum m)
    divisorBudget
    (fun m => SqrtCofactorAPResidueClassElementaryPointBudget m)
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus_of_elementaryPointAPSplitSurplus
      smallBudget divisorBudget hsurplus)

/-- For any chosen small-residue and divisor-error budgets, the elementary
point-count AP split is exact-strength when stated over minimal
counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus_iff_explicitLowerBound50000
    (smallBudget divisorBudget : Nat → Nat) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
        smallBudget divisorBudget ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P := fun m =>
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
          m (smallBudget m) (divisorBudget m))
      (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
        smallBudget divisorBudget))

/-- Exact small-residue budget at the square-root threshold. -/
def LowerHalfPrimeSmallResidueClassSqrtExactBudget
    (m : Nat) : Nat :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m)

/-- The exact small-residue budget supplies the named small-budget target. -/
theorem lowerHalfPrimeSmallResidueClassSqrtBudget_exactBudget
    (m : Nat) :
    LowerHalfPrimeSmallResidueClassSqrtBudget m
      (LowerHalfPrimeSmallResidueClassSqrtExactBudget m) := by
  unfold LowerHalfPrimeSmallResidueClassSqrtBudget
  unfold LowerHalfPrimeSmallResidueClassSqrtExactBudget
  exact le_rfl

/-- Exact square-root divisor-error budget. -/
def SqrtCofactorPrimeCountingDivisorExactBudget
    (m : Nat) : Nat :=
  (Nat.sqrt m - 1) * (Nat.primeCounting (Nat.sqrt m) + 1)

/-- The exact divisor-error budget supplies the named divisor-error target. -/
theorem sqrtCofactorPrimeCountingDivisorErrorBudget_exactBudget
    (m : Nat) :
    SqrtCofactorPrimeCountingDivisorErrorBudget m
      (SqrtCofactorPrimeCountingDivisorExactBudget m) := by
  unfold SqrtCofactorPrimeCountingDivisorErrorBudget
  unfold SqrtCofactorPrimeCountingDivisorExactBudget
  exact le_rfl

/-- Fully explicit elementary point-count AP split.  The only remaining
content is a single arithmetic inequality combining the exact small-residue
term, the summed elementary AP point budget, and the exact divisor-error
term. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
    (m : Nat) : Prop :=
  LowerHalfPrimeSmallResidueClassSqrtExactBudget m +
      (SqrtCofactorAPResidueClassElementaryPointBudgetSum m +
        SqrtCofactorPrimeCountingDivisorExactBudget m) <
    Nat.primeCounting (m / 2)

/-- The fully explicit elementary point-count AP split supplies the budgeted
elementary point-count AP split. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus_of_explicitSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
      m (LowerHalfPrimeSmallResidueClassSqrtExactBudget m)
      (SqrtCofactorPrimeCountingDivisorExactBudget m) := by
  refine ⟨
    lowerHalfPrimeSmallResidueClassSqrtBudget_exactBudget m,
    sqrtCofactorPrimeCountingDivisorErrorBudget_exactBudget m,
    ?_⟩
  simpa [
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus,
    SqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetMargin] using hsurplus

/-- Minimal-counterexample version of the fully explicit elementary
point-count AP split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
      m

/-- The fully explicit elementary point-count AP split supplies the budgeted
minimal-counterexample elementary point-count AP split. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus_of_explicitSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
      LowerHalfPrimeSmallResidueClassSqrtExactBudget
      SqrtCofactorPrimeCountingDivisorExactBudget := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus_of_explicitSplitSurplus
      (hsurplus m hm)

/-- A future proof of the fully explicit elementary point-count AP split
closes the literal binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
    LowerHalfPrimeSmallResidueClassSqrtExactBudget
    SqrtCofactorPrimeCountingDivisorExactBudget
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus_of_explicitSplitSurplus
      hsurplus)

/-- A future proof of the fully explicit elementary point-count AP split
closes the literal remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus
    LowerHalfPrimeSmallResidueClassSqrtExactBudget
    SqrtCofactorPrimeCountingDivisorExactBudget
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus_of_explicitSplitSurplus
      hsurplus)

/-- The fully explicit elementary point-count AP split is exact-strength when
stated over minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P :=
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus)

/-- A necessary feasibility condition for the fully explicit elementary
point-count AP split: the exact divisor-error term alone must be below the
available lower-half prime count. -/
def SqrtCofactorPrimeCountingDivisorExactBudgetFeasible
    (m : Nat) : Prop :=
  SqrtCofactorPrimeCountingDivisorExactBudget m <
    Nat.primeCounting (m / 2)

/-- A necessary feasibility condition for the fully explicit elementary
point-count AP split: the summed elementary AP point budget alone must be
below the available lower-half prime count. -/
def SqrtCofactorAPResidueClassElementaryPointBudgetSumFeasible
    (m : Nat) : Prop :=
  SqrtCofactorAPResidueClassElementaryPointBudgetSum m <
    Nat.primeCounting (m / 2)

/-- The fully explicit elementary point-count AP split forces both large
remainder components to be individually feasible. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility
    (m : Nat) : Prop :=
  SqrtCofactorAPResidueClassElementaryPointBudgetSumFeasible m ∧
    SqrtCofactorPrimeCountingDivisorExactBudgetFeasible m

/-- The disjunctive obstruction to component feasibility for the fully
explicit elementary point-count AP split: at least one large component already
reaches the available lower-half prime count. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction
    (m : Nat) : Prop :=
  Nat.primeCounting (m / 2) ≤
      SqrtCofactorAPResidueClassElementaryPointBudgetSum m ∨
    Nat.primeCounting (m / 2) ≤
      SqrtCofactorPrimeCountingDivisorExactBudget m

/-- The fully explicit elementary point-count AP split implies divisor-error
feasibility.  Failure of this smaller inequality is an immediate obstruction
to this branch. -/
theorem sqrtCofactorPrimeCountingDivisorExactBudgetFeasible_of_elementaryPointAPExplicitSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
        m) :
    SqrtCofactorPrimeCountingDivisorExactBudgetFeasible m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus at hsurplus
  unfold SqrtCofactorPrimeCountingDivisorExactBudgetFeasible
  omega

/-- The fully explicit elementary point-count AP split implies elementary AP
point-budget feasibility. -/
theorem sqrtCofactorAPResidueClassElementaryPointBudgetSumFeasible_of_elementaryPointAPExplicitSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
        m) :
    SqrtCofactorAPResidueClassElementaryPointBudgetSumFeasible m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus at hsurplus
  unfold SqrtCofactorAPResidueClassElementaryPointBudgetSumFeasible
  omega

/-- The fully explicit elementary point-count AP split implies the component
feasibility pair. -/
theorem elementaryPointAPComponentFeasibility_of_elementaryPointAPExplicitSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility
      m :=
  ⟨sqrtCofactorAPResidueClassElementaryPointBudgetSumFeasible_of_elementaryPointAPExplicitSplitSurplus
      hsurplus,
    sqrtCofactorPrimeCountingDivisorExactBudgetFeasible_of_elementaryPointAPExplicitSplitSurplus
      hsurplus⟩

/-- If the exact divisor-error term already reaches the available lower-half
prime count, then the fully explicit elementary point-count AP split cannot
hold. -/
theorem not_elementaryPointAPExplicitSplitSurplus_of_divisorExactBudget_not_feasible
    {m : Nat}
    (hdiv :
      Nat.primeCounting (m / 2) ≤
        SqrtCofactorPrimeCountingDivisorExactBudget m) :
    ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
        m := by
  intro hsurplus
  have hfeasible :=
    sqrtCofactorPrimeCountingDivisorExactBudgetFeasible_of_elementaryPointAPExplicitSplitSurplus
      hsurplus
  unfold SqrtCofactorPrimeCountingDivisorExactBudgetFeasible at hfeasible
  omega

/-- If the summed elementary AP point budget already reaches the available
lower-half prime count, then the fully explicit elementary point-count AP
split cannot hold. -/
theorem not_elementaryPointAPExplicitSplitSurplus_of_APBudgetSum_not_feasible
    {m : Nat}
    (hap :
      Nat.primeCounting (m / 2) ≤
        SqrtCofactorAPResidueClassElementaryPointBudgetSum m) :
    ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
        m := by
  intro hsurplus
  have hfeasible :=
    sqrtCofactorAPResidueClassElementaryPointBudgetSumFeasible_of_elementaryPointAPExplicitSplitSurplus
      hsurplus
  unfold SqrtCofactorAPResidueClassElementaryPointBudgetSumFeasible at hfeasible
  omega

/-- Failure of either component feasibility condition obstructs the fully
explicit elementary point-count AP split. -/
theorem not_elementaryPointAPExplicitSplitSurplus_of_componentFeasibility_not_feasible
    {m : Nat}
    (hcomponent :
      ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility
        m) :
    ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
        m := by
  intro hsurplus
  exact hcomponent
    (elementaryPointAPComponentFeasibility_of_elementaryPointAPExplicitSplitSurplus
      hsurplus)

/-- The disjunctive component-budget obstruction is exactly the failure of the
component feasibility pair. -/
theorem elementaryPointAPComponentBudgetObstruction_iff_not_componentFeasibility
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction
        m ↔
      ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility
        m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility
    SqrtCofactorAPResidueClassElementaryPointBudgetSumFeasible
    SqrtCofactorPrimeCountingDivisorExactBudgetFeasible
  constructor
  · intro h hfeasible
    rcases h with hap | hdiv <;> omega
  · intro hnot
    by_cases hap :
        Nat.primeCounting (m / 2) ≤
          SqrtCofactorAPResidueClassElementaryPointBudgetSum m
    · exact Or.inl hap
    · right
      by_contra hdiv
      exact hnot ⟨by omega, by omega⟩

/-- The disjunctive component-budget obstruction rules out the fully explicit
elementary point-count AP split. -/
theorem not_elementaryPointAPExplicitSplitSurplus_of_componentBudgetObstruction
    {m : Nat}
    (hcomponent :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction
        m) :
    ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus
        m :=
  not_elementaryPointAPExplicitSplitSurplus_of_componentFeasibility_not_feasible
    ((elementaryPointAPComponentBudgetObstruction_iff_not_componentFeasibility
      m).mp hcomponent)

/-- Minimal-counterexample version of the component feasibility conditions
forced by the fully explicit elementary point-count AP split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility
      m

/-- The fully explicit elementary point-count AP split forces the component
feasibility conditions at every minimal counterexample. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility_of_explicitSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility := by
  intro m hm
  exact
    elementaryPointAPComponentFeasibility_of_elementaryPointAPExplicitSplitSurplus
      (hsurplus m hm)

/-- A single minimal counterexample violating the component feasibility pair
rules out the fully explicit elementary point-count AP split route. -/
theorem not_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus_of_exists_minimalCounterexample_not_componentFeasibility
    (hbad :
      ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
        ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility
          m) :
    ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus := by
  intro hsurplus
  rcases hbad with ⟨m, hm, hcomponent⟩
  exact hcomponent
    (elementaryPointAPComponentFeasibility_of_elementaryPointAPExplicitSplitSurplus
      (hsurplus m hm))

/-- A single minimal counterexample where the exact divisor-error budget
already reaches the lower-half prime count rules out the fully explicit
elementary point-count AP split route. -/
theorem not_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus_of_exists_minimalCounterexample_divisorExactBudget_not_feasible
    (hbad :
      ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
        Nat.primeCounting (m / 2) ≤
          SqrtCofactorPrimeCountingDivisorExactBudget m) :
    ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus := by
  intro hsurplus
  rcases hbad with ⟨m, hm, hdiv⟩
  exact
    not_elementaryPointAPExplicitSplitSurplus_of_divisorExactBudget_not_feasible
      hdiv (hsurplus m hm)

/-- A single minimal counterexample where the summed elementary AP point budget
already reaches the lower-half prime count rules out the fully explicit
elementary point-count AP split route. -/
theorem not_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus_of_exists_minimalCounterexample_APBudgetSum_not_feasible
    (hbad :
      ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
        Nat.primeCounting (m / 2) ≤
          SqrtCofactorAPResidueClassElementaryPointBudgetSum m) :
    ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus := by
  intro hsurplus
  rcases hbad with ⟨m, hm, hap⟩
  exact
    not_elementaryPointAPExplicitSplitSurplus_of_APBudgetSum_not_feasible
      hap (hsurplus m hm)

/-- Minimal-counterexample package for the disjunctive component-budget
obstruction to the fully explicit elementary point-count AP split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction :
    Prop :=
  ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction
      m

/-- The minimal-counterexample component-budget obstruction is exactly the
existence of a minimal counterexample where component feasibility fails. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction_iff_exists_minimalCounterexample_not_componentFeasibility :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction ↔
      ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
        ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentFeasibility
          m := by
  constructor
  · rintro ⟨m, hm, hcomponent⟩
    exact
      ⟨m, hm,
        (elementaryPointAPComponentBudgetObstruction_iff_not_componentFeasibility
          m).mp hcomponent⟩
  · rintro ⟨m, hm, hcomponent⟩
    exact
      ⟨m, hm,
        (elementaryPointAPComponentBudgetObstruction_iff_not_componentFeasibility
          m).mpr hcomponent⟩

/-- A single minimal counterexample satisfying the disjunctive component-budget
obstruction rules out the fully explicit elementary point-count AP split route. -/
theorem not_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus_of_componentBudgetObstruction
    (hbad :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction) :
    ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus := by
  intro hsurplus
  rcases hbad with ⟨m, hm, hcomponent⟩
  exact
    not_elementaryPointAPExplicitSplitSurplus_of_componentBudgetObstruction
      hcomponent (hsurplus m hm)

/-- The minimal-counterexample component-budget obstruction is incompatible
with the literal remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem not_explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction
    (hbad :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPComponentBudgetObstruction) :
    ¬ ExplicitGoldbachLowerBound 50000 := by
  intro htarget
  have hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus :=
    (minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus_iff_explicitLowerBound50000).mpr
      htarget
  exact
    not_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus_of_componentBudgetObstruction
      hbad hsurplus

/-- Side-condition-free square-root box criterion.  This is a coarser fixed
`R = sqrt m` target than the exact cofactor-pair count, replacing it by the
rectangular product `#PrimeModuliBelowAbove m (sqrt m) * #Icc 2 (sqrt m)`. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (PrimeModuliBelowAbove m (Nat.sqrt m)).card *
        (Finset.Icc 2 (Nat.sqrt m)).card <
    (LowerHalfPrimes m).card

/-- The fixed square-root box criterion supplies the exact square-root
cofactor criterion. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus_of_sqrtCofactorBoxSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus m := by
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus at hsurplus
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus
  exact lt_of_le_of_lt
    (Nat.add_le_add_left
      (largeBadLowerHalfPrimeCofactorPairs_card_le_sqrtCofactorBoxProduct m)
      (BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m)))
    hsurplus

/-- Minimal-counterexample version of the fixed square-root box criterion. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus m

/-- The fixed square-root box handoff supplies the fixed square-root exact
cofactor handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_of_sqrtCofactorBoxSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus := by
  intro m hm
  exact
    lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus_of_sqrtCofactorBoxSplitSurplus
      (hsurplus m hm)

/-- A future proof of the fixed square-root box handoff closes the literal
binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorBoxSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_of_sqrtCofactorBoxSplitSurplus
      hsurplus)

/-- A future proof of the fixed square-root box handoff closes the literal
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorBoxSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus
    (minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_of_sqrtCofactorBoxSplitSurplus
      hsurplus)

/-- The fixed square-root box handoff is exact-strength when stated over
minimal counterexamples.  This records a coarse but side-condition-free target
whose proof would close the current tail goal. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorBoxSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P := LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorBoxSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorBoxSplitSurplus)

/-- Side-condition-free full prime-counting criterion at the square-root
threshold.  For minimal counterexamples the omitted side condition
`Nat.sqrt m < m` is automatic from `50000 < m`. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      (Nat.primeCounting (m - 1) - Nat.primeCounting (Nat.sqrt m)) *
        (m / (Nat.sqrt m + 1) - 1) <
    Nat.primeCounting (m / 2)

/-- For `1 < m`, the side-condition-free square-root prime-counting
criterion is exactly the existing full prime-counting local criterion with
`R = Nat.sqrt m`. -/
theorem lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus_iff_cofactorPrimeCountingFullSplitSurplus_at_sqrt
    {m : Nat} (hm : 1 < m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
        m ↔
      LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
        m (Nat.sqrt m) := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
    LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus
  exact ⟨fun hineq => ⟨Nat.sqrt_lt_self hm, hineq⟩, fun hsurplus => hsurplus.2⟩

/-- Fixed square-root version of the full prime-counting minimal-counterexample
handoff.  A future proof of this single-threshold inequality for every
minimal counterexample is enough to close the existing existential-threshold
full prime-counting obligation. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
      m

/-- The fixed square-root full prime-counting handoff supplies the existing
full prime-counting minimal-counterexample handoff. -/
theorem minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_sqrtCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus := by
  intro m hm
  refine ⟨Nat.sqrt m, ?_⟩
  have hm_one : 1 < m := by
    have hmgt : 50000 < m := hm.2.1
    omega
  exact
    (lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus_iff_cofactorPrimeCountingFullSplitSurplus_at_sqrt
      hm_one).mp (hsurplus m hm)

/-- A future proof of the fixed square-root full prime-counting handoff closes
the literal binary Goldbach statement. -/
theorem binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus) :
    Round1Status.BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus
    (minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_sqrtCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- A future proof of the fixed square-root full prime-counting handoff closes
the literal remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus) :
    ExplicitGoldbachLowerBound 50000 :=
  explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus
    (minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_sqrtCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- The fixed square-root full prime-counting handoff is exact-strength when
stated over minimal counterexamples: it is equivalent to the remaining
`ExplicitGoldbachLowerBound 50000` target.  This is a diagnostic, not a proof
of the required prime-counting inequality. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus ↔
      ExplicitGoldbachLowerBound 50000 := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus] using
    (minimalCounterexampleObligation_iff_explicitLowerBound50000
      (P := LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus)
      binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus)

/-- The fixed square-root prime-counting full split's box-product component. -/
def SqrtCofactorPrimeCountingFullBoxProductBudget
    (m : Nat) : Nat :=
  (Nat.primeCounting (m - 1) - Nat.primeCounting (Nat.sqrt m)) *
    (m / (Nat.sqrt m + 1) - 1)

/-- Necessary feasibility for the fixed square-root prime-counting full split:
the exact small-residue contribution alone must be below the lower-half prime
count. -/
def SqrtCofactorPrimeCountingFullSmallResidueBudgetFeasible
    (m : Nat) : Prop :=
  BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) <
    Nat.primeCounting (m / 2)

/-- Necessary feasibility for the fixed square-root prime-counting full split:
the box-product component alone must be below the lower-half prime count. -/
def SqrtCofactorPrimeCountingFullBoxProductBudgetFeasible
    (m : Nat) : Prop :=
  SqrtCofactorPrimeCountingFullBoxProductBudget m <
    Nat.primeCounting (m / 2)

/-- Component feasibility pair forced by the fixed square-root prime-counting
full split. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentFeasibility
    (m : Nat) : Prop :=
  SqrtCofactorPrimeCountingFullSmallResidueBudgetFeasible m ∧
    SqrtCofactorPrimeCountingFullBoxProductBudgetFeasible m

/-- Disjunctive component-budget obstruction to the fixed square-root
prime-counting full split: one component already reaches the available
lower-half prime count. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction
    (m : Nat) : Prop :=
  Nat.primeCounting (m / 2) ≤
      BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) ∨
    Nat.primeCounting (m / 2) ≤
      SqrtCofactorPrimeCountingFullBoxProductBudget m

/-- The fixed square-root prime-counting full split implies small-residue
component feasibility. -/
theorem sqrtCofactorPrimeCountingFullSmallResidueBudgetFeasible_of_sqrtCofactorPrimeCountingFullSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
        m) :
    SqrtCofactorPrimeCountingFullSmallResidueBudgetFeasible m := by
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus at hsurplus
  unfold SqrtCofactorPrimeCountingFullSmallResidueBudgetFeasible
  omega

/-- The fixed square-root prime-counting full split implies box-product
component feasibility. -/
theorem sqrtCofactorPrimeCountingFullBoxProductBudgetFeasible_of_sqrtCofactorPrimeCountingFullSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
        m) :
    SqrtCofactorPrimeCountingFullBoxProductBudgetFeasible m := by
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus at hsurplus
  unfold
    SqrtCofactorPrimeCountingFullBoxProductBudgetFeasible
    SqrtCofactorPrimeCountingFullBoxProductBudget
  omega

/-- The fixed square-root prime-counting full split implies component
feasibility. -/
theorem sqrtCofactorPrimeCountingFullComponentFeasibility_of_sqrtCofactorPrimeCountingFullSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentFeasibility
      m :=
  ⟨sqrtCofactorPrimeCountingFullSmallResidueBudgetFeasible_of_sqrtCofactorPrimeCountingFullSplitSurplus
      hsurplus,
    sqrtCofactorPrimeCountingFullBoxProductBudgetFeasible_of_sqrtCofactorPrimeCountingFullSplitSurplus
      hsurplus⟩

/-- The fixed square-root prime-counting full component-budget obstruction is
exactly the failure of the corresponding component feasibility pair. -/
theorem sqrtCofactorPrimeCountingFullComponentBudgetObstruction_iff_not_componentFeasibility
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction
        m ↔
      ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentFeasibility
        m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentFeasibility
    SqrtCofactorPrimeCountingFullSmallResidueBudgetFeasible
    SqrtCofactorPrimeCountingFullBoxProductBudgetFeasible
  constructor
  · intro h hfeasible
    rcases h with hsmall | hbox <;> omega
  · intro hnot
    by_cases hsmall :
        Nat.primeCounting (m / 2) ≤
          BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m)
    · exact Or.inl hsmall
    · right
      by_contra hbox
      exact hnot ⟨by omega, by omega⟩

/-- The fixed square-root prime-counting full component-budget obstruction
rules out the local split. -/
theorem not_sqrtCofactorPrimeCountingFullSplitSurplus_of_componentBudgetObstruction
    {m : Nat}
    (hcomponent :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction
        m) :
    ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
        m := by
  intro hsurplus
  have hnot :
      ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentFeasibility
        m :=
    (sqrtCofactorPrimeCountingFullComponentBudgetObstruction_iff_not_componentFeasibility
      m).mp hcomponent
  exact hnot
    (sqrtCofactorPrimeCountingFullComponentFeasibility_of_sqrtCofactorPrimeCountingFullSplitSurplus
      hsurplus)

/-- Minimal-counterexample package for the fixed square-root prime-counting
full component-budget obstruction. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction :
    Prop :=
  ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction
      m

/-- The minimal-counterexample fixed square-root prime-counting full
component-budget obstruction is exactly the existence of a minimal
counterexample where component feasibility fails. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullComponentBudgetObstruction_iff_exists_minimalCounterexample_not_componentFeasibility :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction ↔
      ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
        ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentFeasibility
          m := by
  constructor
  · rintro ⟨m, hm, hcomponent⟩
    exact
      ⟨m, hm,
        (sqrtCofactorPrimeCountingFullComponentBudgetObstruction_iff_not_componentFeasibility
          m).mp hcomponent⟩
  · rintro ⟨m, hm, hcomponent⟩
    exact
      ⟨m, hm,
        (sqrtCofactorPrimeCountingFullComponentBudgetObstruction_iff_not_componentFeasibility
          m).mpr hcomponent⟩

/-- A minimal counterexample satisfying the fixed square-root prime-counting
full component-budget obstruction rules out that exact-strength handoff. -/
theorem not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus_of_componentBudgetObstruction
    (hbad :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction) :
    ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus := by
  intro hsurplus
  rcases hbad with ⟨m, hm, hcomponent⟩
  exact
    not_sqrtCofactorPrimeCountingFullSplitSurplus_of_componentBudgetObstruction
      hcomponent (hsurplus m hm)

/-- The minimal-counterexample fixed square-root prime-counting full
component-budget obstruction is incompatible with the literal remaining
`ExplicitGoldbachLowerBound 50000` target. -/
theorem not_explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullComponentBudgetObstruction
    (hbad :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction) :
    ¬ ExplicitGoldbachLowerBound 50000 := by
  intro htarget
  have hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus :=
    (minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000).mpr
      htarget
  exact
    not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus_of_componentBudgetObstruction
      hbad hsurplus

/-- Exact total-budget obstruction to the fixed square-root prime-counting full
split: the two explicit components together already reach the available
lower-half prime count. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
    (m : Nat) : Prop :=
  Nat.primeCounting (m / 2) ≤
    BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
      SqrtCofactorPrimeCountingFullBoxProductBudget m

/-- The total-budget obstruction is exactly the negation of the fixed
square-root prime-counting full split. -/
theorem sqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_splitSurplus
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
        m ↔
      ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
        m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
    SqrtCofactorPrimeCountingFullBoxProductBudget
  omega

/-- Component-budget failure is a special case of total-budget obstruction. -/
theorem sqrtCofactorPrimeCountingFullBudgetObstruction_of_componentBudgetObstruction
    {m : Nat}
    (hcomponent :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
      m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
    SqrtCofactorPrimeCountingFullBoxProductBudget at *
  rcases hcomponent with hsmall | hbox <;> omega

/-- Minimal-counterexample package for exact total-budget obstruction to the
fixed square-root prime-counting full split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction :
    Prop :=
  ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
      m

/-- Component-budget obstruction lifts into exact total-budget obstruction at
the minimal-counterexample layer. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_of_componentBudgetObstruction
    (hbad :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullComponentBudgetObstruction) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction := by
  rcases hbad with ⟨m, hm, hcomponent⟩
  exact
    ⟨m, hm,
      sqrtCofactorPrimeCountingFullBudgetObstruction_of_componentBudgetObstruction
        hcomponent⟩

/-- Exact total-budget obstruction is precisely the failure of the
exact-strength fixed square-root prime-counting full handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_splitSurplus :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction ↔
      ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus := by
  constructor
  · rintro ⟨m, hm, hbudget⟩ hsurplus
    exact
      (sqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_splitSurplus
        m).mp hbudget (hsurplus m hm)
  · intro hnot
    classical
    have hnot_exists :
        ∃ m : Nat,
          ¬ (MinimalBinaryGoldbachCounterexample m →
            LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
              m) :=
      not_forall.mp hnot
    rcases hnot_exists with ⟨m, hmnot⟩
    have hm : MinimalBinaryGoldbachCounterexample m := by
      by_contra hminimal
      exact hmnot (fun h => False.elim (hminimal h))
    have hnotSurplus :
        ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
          m := by
      intro hsurplus
      exact hmnot (fun _ => hsurplus)
    exact
      ⟨m, hm,
        (sqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_splitSurplus
          m).mpr hnotSurplus⟩

/-- The exact total-budget obstruction is equivalent to failure of the literal
remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction ↔
      ¬ ExplicitGoldbachLowerBound 50000 := by
  constructor
  · intro hbudget htarget
    have hsurplus :
        MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus :=
      (minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000).mpr
        htarget
    exact
      (minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_splitSurplus).mp
        hbudget hsurplus
  · intro hnotTarget
    have hnotSurplus :
        ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus := by
      intro hsurplus
      exact hnotTarget
        ((minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000).mp
          hsurplus)
    exact
      (minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_splitSurplus).mpr
        hnotSurplus

/-- Positive form of the exact total-budget criterion: the fixed square-root
prime-counting full split is exactly the absence of its total-budget
obstruction. -/
theorem sqrtCofactorPrimeCountingFullSplitSurplus_iff_not_budgetObstruction
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus
        m ↔
      ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
        m := by
  constructor
  · intro hsplit hbudget
    exact
      (sqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_splitSurplus
        m).mp hbudget hsplit
  · intro hnotBudget
    classical
    by_contra hsplit
    exact hnotBudget
      ((sqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_splitSurplus
        m).mpr hsplit)

/-- Minimal-counterexample positive form: the exact-strength fixed square-root
prime-counting full handoff is equivalent to absence of the exact total-budget
obstruction. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus_iff_not_budgetObstruction :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus ↔
      ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction := by
  constructor
  · intro hsplit hbudget
    exact
      (minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_splitSurplus).mp
        hbudget hsplit
  · intro hnotBudget
    classical
    by_contra hsplit
    exact hnotBudget
      ((minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_splitSurplus).mpr
        hsplit)

/-- The remaining literal target is equivalent to the absence of the exact
fixed square-root prime-counting full total-budget obstruction. -/
theorem explicitLowerBound50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction :
    ExplicitGoldbachLowerBound 50000 ↔
      ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction := by
  constructor
  · intro htarget hbudget
    exact
      (minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_explicitLowerBound50000).mp
        hbudget htarget
  · intro hnotBudget
    classical
    by_contra htarget
    exact hnotBudget
      ((minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_explicitLowerBound50000).mpr
        htarget)

/-- Conjecture-level positive form: after the `50000` certificate, the literal
binary Goldbach statement is equivalent to absence of the exact fixed
square-root prime-counting full total-budget obstruction. -/
theorem binaryGoldbachConjecture_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction :
    Round1Status.BinaryGoldbachConjecture ↔
      ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction :=
  Round1Status.binaryGoldbachConjecture_iff_explicitLowerBound50000_of_chunkedCertificate2To50000.trans
    explicitLowerBound50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction

/-- Conjecture-level obstruction form: the exact fixed square-root
prime-counting full total-budget obstruction is precisely the failure of the
literal binary Goldbach statement. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_binaryGoldbachConjecture :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction ↔
      ¬ Round1Status.BinaryGoldbachConjecture := by
  exact
    minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_explicitLowerBound50000.trans
      (not_congr
        Round1Status.binaryGoldbachConjecture_iff_explicitLowerBound50000_of_chunkedCertificate2To50000.symm)

/-- Negated conjecture form, useful for counterexample searches: a failure of
the literal binary Goldbach statement is equivalent to existence of the exact
fixed square-root prime-counting full total-budget obstruction. -/
theorem not_binaryGoldbachConjecture_iff_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction :
    ¬ Round1Status.BinaryGoldbachConjecture ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction :=
  minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_binaryGoldbachConjecture.symm

/-- Status-layer positive form: the current `50000` tail target is equivalent
to absence of the exact fixed square-root prime-counting full total-budget
obstruction. -/
theorem currentFormalTarget50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction :
    Round1Status.CurrentFormalTarget50000 ↔
      ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    explicitLowerBound50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction

/-- The exact fixed square-root total-budget obstruction is precisely the
failure of the current `50000` status-layer tail target. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_currentFormalTarget50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction ↔
      ¬ Round1Status.CurrentFormalTarget50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_explicitLowerBound50000

/-- Negated status-layer form: failure of the current `50000` tail target is
equivalent to existence of the exact fixed square-root total-budget
obstruction. -/
theorem not_currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction :
    ¬ Round1Status.CurrentFormalTarget50000 ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction :=
  minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_currentFormalTarget50000.symm

/-- Headline positive form: the project `StrongGoldbach` statement is
equivalent to absence of the exact fixed square-root prime-counting full
total-budget obstruction. -/
theorem strongGoldbach_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction :
    StrongGoldbach ↔
      ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction :=
  Round1Status.binaryGoldbachConjecture_iff_strongGoldbach.symm.trans
    binaryGoldbachConjecture_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction

/-- The exact fixed square-root total-budget obstruction is precisely the
failure of the project `StrongGoldbach` statement. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_strongGoldbach :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction ↔
      ¬ StrongGoldbach := by
  exact
    minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_binaryGoldbachConjecture.trans
      (not_congr Round1Status.binaryGoldbachConjecture_iff_strongGoldbach)

/-- Negated headline form: failure of `StrongGoldbach` is equivalent to the
exact fixed square-root total-budget obstruction. -/
theorem not_strongGoldbach_iff_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction :
    ¬ StrongGoldbach ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction :=
  minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_not_strongGoldbach.symm

/-- Unpacked absence of the exact total-budget obstruction: it is enough, and
also necessary, to rule out the local budget obstruction at every minimal
binary Goldbach counterexample. -/
theorem not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_forall_minimal_not_budgetObstruction :
    ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction ↔
      ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
        ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
          m := by
  constructor
  · intro hno m hm hbudget
    exact hno ⟨m, hm, hbudget⟩
  · intro hforall hpack
    rcases hpack with ⟨m, hm, hbudget⟩
    exact hforall m hm hbudget

/-- The current `50000` tail target in pointwise form: every minimal
counterexample must avoid the exact fixed square-root total-budget
obstruction. -/
theorem currentFormalTarget50000_iff_forall_minimalCounterexample_not_sqrtCofactorPrimeCountingFullBudgetObstruction :
    Round1Status.CurrentFormalTarget50000 ↔
      ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
        ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
          m :=
  currentFormalTarget50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction.trans
    not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_forall_minimal_not_budgetObstruction

/-- The project headline in pointwise form: `StrongGoldbach` is equivalent to
ruling out the exact fixed square-root total-budget obstruction at every
minimal binary Goldbach counterexample. -/
theorem strongGoldbach_iff_forall_minimalCounterexample_not_sqrtCofactorPrimeCountingFullBudgetObstruction :
    StrongGoldbach ↔
      ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
        ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
          m :=
  strongGoldbach_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction.trans
    not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction_iff_forall_minimal_not_budgetObstruction

/-- Negated headline in unpacked form: failure of `StrongGoldbach` is exactly
existence of a minimal binary Goldbach counterexample satisfying the local
exact fixed square-root total-budget obstruction. -/
theorem not_strongGoldbach_iff_exists_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetObstruction :
    ¬ StrongGoldbach ↔
      ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
          m := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction] using
    not_strongGoldbach_iff_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction

/-- Local strict-inequality form: absence of the exact total-budget obstruction
is exactly the statement that the explicit small-residue contribution plus the
fixed square-root cofactor box budget is strictly below the lower-half prime
count. -/
theorem not_sqrtCofactorPrimeCountingFullBudgetObstruction_iff_budgetStrict
    (m : Nat) :
    ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
        m ↔
      BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
        SqrtCofactorPrimeCountingFullBoxProductBudget m <
          Nat.primeCounting (m / 2) := by
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
  omega

/-- The current `50000` tail target as a fully explicit pointwise strict
budget inequality over minimal binary Goldbach counterexamples. -/
theorem currentFormalTarget50000_iff_forall_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetStrict :
    Round1Status.CurrentFormalTarget50000 ↔
      ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
        BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
          SqrtCofactorPrimeCountingFullBoxProductBudget m <
            Nat.primeCounting (m / 2) := by
  constructor
  · intro htarget m hm
    exact
      (not_sqrtCofactorPrimeCountingFullBudgetObstruction_iff_budgetStrict
        m).mp
        ((currentFormalTarget50000_iff_forall_minimalCounterexample_not_sqrtCofactorPrimeCountingFullBudgetObstruction).mp
          htarget m hm)
  · intro hstrict
    exact
      (currentFormalTarget50000_iff_forall_minimalCounterexample_not_sqrtCofactorPrimeCountingFullBudgetObstruction).mpr
        (fun m hm =>
          (not_sqrtCofactorPrimeCountingFullBudgetObstruction_iff_budgetStrict
            m).mpr (hstrict m hm))

/-- The project headline as a fully explicit pointwise strict budget
inequality over minimal binary Goldbach counterexamples. -/
theorem strongGoldbach_iff_forall_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetStrict :
    StrongGoldbach ↔
      ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
        BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
          SqrtCofactorPrimeCountingFullBoxProductBudget m <
            Nat.primeCounting (m / 2) := by
  constructor
  · intro hgoldbach m hm
    exact
      (not_sqrtCofactorPrimeCountingFullBudgetObstruction_iff_budgetStrict
        m).mp
        ((strongGoldbach_iff_forall_minimalCounterexample_not_sqrtCofactorPrimeCountingFullBudgetObstruction).mp
          hgoldbach m hm)
  · intro hstrict
    exact
      (strongGoldbach_iff_forall_minimalCounterexample_not_sqrtCofactorPrimeCountingFullBudgetObstruction).mpr
        (fun m hm =>
          (not_sqrtCofactorPrimeCountingFullBudgetObstruction_iff_budgetStrict
            m).mpr (hstrict m hm))

/-- Negated headline as a fully explicit non-strict budget obstruction:
`StrongGoldbach` fails exactly when some minimal counterexample has the
small-residue contribution plus fixed square-root cofactor box budget already
reach the lower-half prime count. -/
theorem not_strongGoldbach_iff_exists_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetNonStrict :
    ¬ StrongGoldbach ↔
      ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
        Nat.primeCounting (m / 2) ≤
          BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
            SqrtCofactorPrimeCountingFullBoxProductBudget m := by
  simpa [LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction] using
    not_strongGoldbach_iff_exists_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetObstruction

/-- A named budget for the fixed square-root full prime-counting box-product
term. -/
def SqrtCofactorPrimeCountingFullBoxProductBudgetBound
    (m budget : Nat) : Prop :=
  SqrtCofactorPrimeCountingFullBoxProductBudget m ≤ budget

/-- Margin condition for the fixed square-root full prime-counting
two-budget split. -/
def SqrtCofactorPrimeCountingFullTwoBudgetMargin
    (m smallBudget boxBudget : Nat) : Prop :=
  smallBudget + boxBudget < Nat.primeCounting (m / 2)

/-- Budget-split form of the fixed square-root full prime-counting strict
budget target.  It separates the small-residue contribution from the cofactor
box-product contribution and leaves a named arithmetic margin. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetSplitSurplus
    (m smallBudget boxBudget : Nat) : Prop :=
  LowerHalfPrimeSmallResidueClassSqrtBudget m smallBudget ∧
    SqrtCofactorPrimeCountingFullBoxProductBudgetBound m boxBudget ∧
    SqrtCofactorPrimeCountingFullTwoBudgetMargin m smallBudget boxBudget

/-- The two-budget split supplies the explicit strict budget inequality. -/
theorem sqrtCofactorPrimeCountingFullBudgetStrict_of_budgetSplitSurplus
    {m smallBudget boxBudget : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetSplitSurplus
        m smallBudget boxBudget) :
    BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
        SqrtCofactorPrimeCountingFullBoxProductBudget m <
      Nat.primeCounting (m / 2) := by
  rcases hsurplus with ⟨hsmall, hbox, hmargin⟩
  unfold LowerHalfPrimeSmallResidueClassSqrtBudget at hsmall
  unfold SqrtCofactorPrimeCountingFullBoxProductBudgetBound at hbox
  unfold SqrtCofactorPrimeCountingFullTwoBudgetMargin at hmargin
  omega

/-- The two-budget split rules out the local exact total-budget obstruction. -/
theorem not_sqrtCofactorPrimeCountingFullBudgetObstruction_of_budgetSplitSurplus
    {m smallBudget boxBudget : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetSplitSurplus
        m smallBudget boxBudget) :
    ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetObstruction
        m :=
  (not_sqrtCofactorPrimeCountingFullBudgetObstruction_iff_budgetStrict
    m).mpr
    (sqrtCofactorPrimeCountingFullBudgetStrict_of_budgetSplitSurplus hsurplus)

/-- Minimal-counterexample version of the fixed square-root full
prime-counting two-budget split.  Future analytic work may choose the two
budget functions and prove the three named sub-inequalities separately. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetSplitSurplus
    (smallBudget boxBudget : Nat → Nat) : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetSplitSurplus
      m (smallBudget m) (boxBudget m)

/-- A future proof of the fixed square-root full prime-counting two-budget
split closes the current `50000` tail target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetSplitSurplus
    (smallBudget boxBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetSplitSurplus
        smallBudget boxBudget) :
    Round1Status.CurrentFormalTarget50000 := by
  exact
    (currentFormalTarget50000_iff_forall_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetStrict).mpr
      (fun m hm =>
        sqrtCofactorPrimeCountingFullBudgetStrict_of_budgetSplitSurplus
          (hsurplus m hm))

/-- A future proof of the fixed square-root full prime-counting two-budget
split closes the project headline. -/
theorem strongGoldbach_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetSplitSurplus
    (smallBudget boxBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetSplitSurplus
        smallBudget boxBudget) :
    StrongGoldbach := by
  exact
    (strongGoldbach_iff_forall_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetStrict).mpr
      (fun m hm =>
        sqrtCofactorPrimeCountingFullBudgetStrict_of_budgetSplitSurplus
          (hsurplus m hm))

/-- Fully explicit two-budget split using the exact small-residue and
box-product budgets.  This is a diagnostic exact-strength form, not an
analytic estimate. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullExactBudgetSplitSurplus
    (m : Nat) : Prop :=
  LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullBudgetSplitSurplus
    m (LowerHalfPrimeSmallResidueClassSqrtExactBudget m)
      (SqrtCofactorPrimeCountingFullBoxProductBudget m)

/-- The exact-budget split is precisely the explicit strict budget
inequality. -/
theorem sqrtCofactorPrimeCountingFullExactBudgetSplitSurplus_iff_budgetStrict
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullExactBudgetSplitSurplus
        m ↔
      BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m) +
        SqrtCofactorPrimeCountingFullBoxProductBudget m <
          Nat.primeCounting (m / 2) := by
  constructor
  · intro hsurplus
    exact sqrtCofactorPrimeCountingFullBudgetStrict_of_budgetSplitSurplus hsurplus
  · intro hstrict
    refine ⟨lowerHalfPrimeSmallResidueClassSqrtBudget_exactBudget m, ?_, ?_⟩
    · unfold SqrtCofactorPrimeCountingFullBoxProductBudgetBound
      exact le_rfl
    · unfold SqrtCofactorPrimeCountingFullTwoBudgetMargin
      simpa [LowerHalfPrimeSmallResidueClassSqrtExactBudget] using hstrict

/-- Minimal-counterexample version of the fully explicit fixed square-root
full prime-counting exact-budget split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullExactBudgetSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullExactBudgetSplitSurplus
      m

/-- The current `50000` tail target is exactly the minimal-counterexample
fully explicit two-budget split. -/
theorem currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullExactBudgetSplitSurplus :
    Round1Status.CurrentFormalTarget50000 ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullExactBudgetSplitSurplus := by
  constructor
  · intro htarget m hm
    exact
      (sqrtCofactorPrimeCountingFullExactBudgetSplitSurplus_iff_budgetStrict
        m).mpr
        ((currentFormalTarget50000_iff_forall_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetStrict).mp
          htarget m hm)
  · intro hsurplus
    exact
      (currentFormalTarget50000_iff_forall_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetStrict).mpr
        (fun m hm =>
          (sqrtCofactorPrimeCountingFullExactBudgetSplitSurplus_iff_budgetStrict
            m).mp (hsurplus m hm))

/-- The project headline is exactly the minimal-counterexample fully explicit
two-budget split. -/
theorem strongGoldbach_iff_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullExactBudgetSplitSurplus :
    StrongGoldbach ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullExactBudgetSplitSurplus := by
  constructor
  · intro hgoldbach m hm
    exact
      (sqrtCofactorPrimeCountingFullExactBudgetSplitSurplus_iff_budgetStrict
        m).mpr
        ((strongGoldbach_iff_forall_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetStrict).mp
          hgoldbach m hm)
  · intro hsurplus
    exact
      (strongGoldbach_iff_forall_minimalCounterexample_sqrtCofactorPrimeCountingFullBudgetStrict).mpr
        (fun m hm =>
          (sqrtCofactorPrimeCountingFullExactBudgetSplitSurplus_iff_budgetStrict
            m).mp (hsurplus m hm))

/-- At `m = 30`, the fixed square-root full prime-counting box-product
budget is already `28`.  This concrete value shows how coarse the rectangular
box-product replacement is. -/
theorem sqrtCofactorPrimeCountingFullBoxProductBudget_30_eq_28 :
    SqrtCofactorPrimeCountingFullBoxProductBudget 30 = 28 := by
  unfold SqrtCofactorPrimeCountingFullBoxProductBudget
  have hsqrt : Nat.sqrt 30 = 5 := by
    norm_num [Nat.sqrt_eq]
  have hpi29 : Nat.primeCounting 29 = 10 := by
    decide
  have hpi5 : Nat.primeCounting 5 = 3 := by
    decide
  rw [hsqrt, hpi29, hpi5]

/-- The lower-half prime count at `m = 30` is `π(15) = 6`. -/
theorem nat_primeCounting_15_eq_6 :
    Nat.primeCounting 15 = 6 := by
  decide

/-- Concrete catch for the fixed square-root full prime-counting
box-product route: its exact-budget local split already fails at `m = 30`.
This does not refute the minimal-counterexample reformulation; it records that
the box-product split is not a universal local inequality to prove directly. -/
theorem not_sqrtCofactorPrimeCountingFullExactBudgetSplitSurplus_30 :
    ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullExactBudgetSplitSurplus
        30 := by
  intro hsurplus
  have hstrict :=
    (sqrtCofactorPrimeCountingFullExactBudgetSplitSurplus_iff_budgetStrict
      30).mp hsurplus
  rw [sqrtCofactorPrimeCountingFullBoxProductBudget_30_eq_28,
    nat_primeCounting_15_eq_6] at hstrict
  omega

/-- Existence form of the same catch: the fixed square-root full
prime-counting exact-budget split is not valid for all natural numbers. -/
theorem not_forall_sqrtCofactorPrimeCountingFullExactBudgetSplitSurplus :
    ¬ ∀ m : Nat,
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPrimeCountingFullExactBudgetSplitSurplus
        m := by
  intro hforall
  exact not_sqrtCofactorPrimeCountingFullExactBudgetSplitSurplus_30
    (hforall 30)

/-- A named budget for the exact fixed square-root cofactor-pair count.  This
keeps the genuine cofactor relation rather than replacing it by the
rectangular box-product overcount. -/
def SqrtCofactorPairBudgetBound
    (m budget : Nat) : Prop :=
  (LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).card ≤ budget

/-- Margin condition for the exact fixed square-root cofactor-pair two-budget
split, with the lower-half prime count written as `π(m / 2)`. -/
def SqrtCofactorPairTwoBudgetMargin
    (m smallBudget cofactorBudget : Nat) : Prop :=
  smallBudget + cofactorBudget < Nat.primeCounting (m / 2)

/-- Budget-split form of the exact fixed square-root cofactor-pair handoff.
It separates the small-residue contribution from the exact cofactor-pair
count and leaves a named arithmetic margin. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPairBudgetSplitSurplus
    (m smallBudget cofactorBudget : Nat) : Prop :=
  LowerHalfPrimeSmallResidueClassSqrtBudget m smallBudget ∧
    SqrtCofactorPairBudgetBound m cofactorBudget ∧
    SqrtCofactorPairTwoBudgetMargin m smallBudget cofactorBudget

/-- The exact cofactor-pair two-budget split supplies the fixed square-root
exact cofactor handoff. -/
theorem sqrtCofactorSplitSurplus_of_pairBudgetSplitSurplus
    {m smallBudget cofactorBudget : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPairBudgetSplitSurplus
        m smallBudget cofactorBudget) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus m := by
  rcases hsurplus with ⟨hsmall, hcofactor, hmargin⟩
  unfold LowerHalfPrimeSmallResidueClassSqrtBudget at hsmall
  unfold SqrtCofactorPairBudgetBound at hcofactor
  unfold SqrtCofactorPairTwoBudgetMargin at hmargin
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus
  rw [lowerHalfPrimes_card_eq_primeCounting_half]
  omega

/-- Minimal-counterexample version of the exact fixed square-root
cofactor-pair budget split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPairBudgetSplitSurplus
    (smallBudget cofactorBudget : Nat → Nat) : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPairBudgetSplitSurplus
      m (smallBudget m) (cofactorBudget m)

/-- A future proof of the exact cofactor-pair budget split closes the exact
fixed square-root cofactor handoff. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_of_pairBudgetSplitSurplus
    (smallBudget cofactorBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPairBudgetSplitSurplus
        smallBudget cofactorBudget) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus := by
  intro m hm
  exact sqrtCofactorSplitSurplus_of_pairBudgetSplitSurplus (hsurplus m hm)

/-- A future proof of the exact cofactor-pair budget split closes the current
`50000` tail target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSqrtCofactorPairBudgetSplitSurplus
    (smallBudget cofactorBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPairBudgetSplitSurplus
        smallBudget cofactorBudget) :
    Round1Status.CurrentFormalTarget50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus
      (minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_of_pairBudgetSplitSurplus
        smallBudget cofactorBudget hsurplus)

/-- A future proof of the exact cofactor-pair budget split closes the project
headline. -/
theorem strongGoldbach_of_minimalCounterexampleFiniteResidueSqrtCofactorPairBudgetSplitSurplus
    (smallBudget cofactorBudget : Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPairBudgetSplitSurplus
        smallBudget cofactorBudget) :
    StrongGoldbach :=
  Round1Status.binaryGoldbachConjecture_iff_strongGoldbach.mp
    (binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus
      (minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_of_pairBudgetSplitSurplus
        smallBudget cofactorBudget hsurplus))

/-- Fully explicit exact cofactor-pair budget split using the exact
small-residue and exact cofactor-pair budgets. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPairExactBudgetSplitSurplus
    (m : Nat) : Prop :=
  LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPairBudgetSplitSurplus
    m (LowerHalfPrimeSmallResidueClassSqrtExactBudget m)
      ((LargeBadLowerHalfPrimeCofactorPairs m (Nat.sqrt m)).card)

/-- The fully explicit exact cofactor-pair budget split is exactly the fixed
square-root exact cofactor handoff. -/
theorem sqrtCofactorPairExactBudgetSplitSurplus_iff_sqrtCofactorSplitSurplus
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPairExactBudgetSplitSurplus
        m ↔
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus m := by
  constructor
  · intro hsurplus
    exact sqrtCofactorSplitSurplus_of_pairBudgetSplitSurplus hsurplus
  · intro hsurplus
    refine ⟨lowerHalfPrimeSmallResidueClassSqrtBudget_exactBudget m, ?_, ?_⟩
    · unfold SqrtCofactorPairBudgetBound
      exact le_rfl
    · unfold SqrtCofactorPairTwoBudgetMargin
      unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus at hsurplus
      rw [lowerHalfPrimes_card_eq_primeCounting_half] at hsurplus
      simpa [LowerHalfPrimeSmallResidueClassSqrtExactBudget] using hsurplus

/-- Minimal-counterexample version of the fully explicit exact cofactor-pair
budget split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPairExactBudgetSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPairExactBudgetSplitSurplus
      m

/-- The fully explicit exact cofactor-pair budget split is exact-strength:
over minimal counterexamples it is equivalent to the current `50000` tail
target. -/
theorem currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorPairExactBudgetSplitSurplus :
    Round1Status.CurrentFormalTarget50000 ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPairExactBudgetSplitSurplus := by
  constructor
  · intro htarget m hm
    have hsplit :
        MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus :=
      (minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_iff_explicitLowerBound50000).mpr
        (by simpa [Round1Status.CurrentFormalTarget50000] using htarget)
    exact
      (sqrtCofactorPairExactBudgetSplitSurplus_iff_sqrtCofactorSplitSurplus
        m).mpr (hsplit m hm)
  · intro hsurplus
    have hsplit :
        MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus := by
      intro m hm
      exact
        (sqrtCofactorPairExactBudgetSplitSurplus_iff_sqrtCofactorSplitSurplus
          m).mp (hsurplus m hm)
    simpa [Round1Status.CurrentFormalTarget50000] using
      (minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_iff_explicitLowerBound50000).mp
        hsplit

/-- The fully explicit exact cofactor-pair budget split is also equivalent to
the project headline. -/
theorem strongGoldbach_iff_minimalCounterexampleFiniteResidueSqrtCofactorPairExactBudgetSplitSurplus :
    StrongGoldbach ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPairExactBudgetSplitSurplus := by
  exact
    Round1Status.binaryGoldbachConjecture_iff_strongGoldbach.symm.trans
      (binaryGoldbachConjecture_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction.trans
        (currentFormalTarget50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullBudgetObstruction.symm.trans
          currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorPairExactBudgetSplitSurplus))

/-- A pointwise budget for each fixed square-root cofactor fiber. -/
def SqrtCofactorFiberPointwiseBudget
    (m : Nat) (fiberBudget : Nat → Nat) : Prop :=
  ∀ k : Nat, k ∈ Finset.Icc 2 (Nat.sqrt m) →
    (LargeBadLowerHalfPrimeSqrtCofactorFiber m k).card ≤ fiberBudget k

/-- The sum of the pointwise cofactor-fiber budgets stays inside the assigned
total cofactor-pair budget. -/
def SqrtCofactorFiberPointwiseBudgetSum
    (m : Nat) (fiberBudget : Nat → Nat) (cofactorBudget : Nat) : Prop :=
  (Finset.Icc 2 (Nat.sqrt m)).sum fiberBudget ≤ cofactorBudget

/-- Pointwise cofactor-fiber budgets supply the exact cofactor-pair budget. -/
theorem sqrtCofactorPairBudgetBound_of_fiberPointwiseBudget
    {m cofactorBudget : Nat} {fiberBudget : Nat → Nat}
    (hpoint : SqrtCofactorFiberPointwiseBudget m fiberBudget)
    (hsum : SqrtCofactorFiberPointwiseBudgetSum m fiberBudget cofactorBudget) :
    SqrtCofactorPairBudgetBound m cofactorBudget := by
  unfold SqrtCofactorPairBudgetBound
  rw [largeBadLowerHalfPrimeCofactorPairs_card_eq_sum_fibers_at_sqrt]
  unfold SqrtCofactorFiberPointwiseBudget at hpoint
  unfold SqrtCofactorFiberPointwiseBudgetSum at hsum
  exact le_trans (Finset.sum_le_sum fun k hk => hpoint k hk) hsum

/-- Fiber-budget form of the exact fixed square-root cofactor-pair handoff.
This separates the small-residue budget, each fixed-`k` cofactor fiber
budget, the fiber-budget summation, and the final two-budget margin. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetSplitSurplus
    (m smallBudget cofactorBudget : Nat) (fiberBudget : Nat → Nat) : Prop :=
  LowerHalfPrimeSmallResidueClassSqrtBudget m smallBudget ∧
    SqrtCofactorFiberPointwiseBudget m fiberBudget ∧
    SqrtCofactorFiberPointwiseBudgetSum m fiberBudget cofactorBudget ∧
    SqrtCofactorPairTwoBudgetMargin m smallBudget cofactorBudget

/-- The fiber-budget split supplies the exact cofactor-pair two-budget split. -/
theorem sqrtCofactorPairBudgetSplitSurplus_of_fiberBudgetSplitSurplus
    {m smallBudget cofactorBudget : Nat} {fiberBudget : Nat → Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetSplitSurplus
        m smallBudget cofactorBudget fiberBudget) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPairBudgetSplitSurplus
      m smallBudget cofactorBudget := by
  rcases hsurplus with ⟨hsmall, hpoint, hsum, hmargin⟩
  exact
    ⟨hsmall,
      sqrtCofactorPairBudgetBound_of_fiberPointwiseBudget hpoint hsum,
      hmargin⟩

/-- The fiber-budget split supplies the fixed square-root exact cofactor
handoff. -/
theorem sqrtCofactorSplitSurplus_of_fiberBudgetSplitSurplus
    {m smallBudget cofactorBudget : Nat} {fiberBudget : Nat → Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetSplitSurplus
        m smallBudget cofactorBudget fiberBudget) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorSplitSurplus m :=
  sqrtCofactorSplitSurplus_of_pairBudgetSplitSurplus
    (sqrtCofactorPairBudgetSplitSurplus_of_fiberBudgetSplitSurplus
      hsurplus)

/-- Minimal-counterexample version of the cofactor-fiber budget split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetSplitSurplus
    (smallBudget cofactorBudget : Nat → Nat)
    (fiberBudget : Nat → Nat → Nat) : Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetSplitSurplus
      m (smallBudget m) (cofactorBudget m) (fiberBudget m)

/-- The cofactor-fiber budget split supplies the exact cofactor-pair
budget-split handoff over minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorPairBudgetSplitSurplus_of_fiberBudgetSplitSurplus
    (smallBudget cofactorBudget : Nat → Nat)
    (fiberBudget : Nat → Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetSplitSurplus
        smallBudget cofactorBudget fiberBudget) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPairBudgetSplitSurplus
      smallBudget cofactorBudget := by
  intro m hm
  exact
    sqrtCofactorPairBudgetSplitSurplus_of_fiberBudgetSplitSurplus
      (hsurplus m hm)

/-- A future proof of the cofactor-fiber budget split closes the current
`50000` tail target. -/
theorem currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetSplitSurplus
    (smallBudget cofactorBudget : Nat → Nat)
    (fiberBudget : Nat → Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetSplitSurplus
        smallBudget cofactorBudget fiberBudget) :
    Round1Status.CurrentFormalTarget50000 :=
  currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSqrtCofactorPairBudgetSplitSurplus
    smallBudget cofactorBudget
    (minimalCounterexampleFiniteResidueSqrtCofactorPairBudgetSplitSurplus_of_fiberBudgetSplitSurplus
      smallBudget cofactorBudget fiberBudget hsurplus)

/-- A future proof of the cofactor-fiber budget split closes the project
headline. -/
theorem strongGoldbach_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetSplitSurplus
    (smallBudget cofactorBudget : Nat → Nat)
    (fiberBudget : Nat → Nat → Nat)
    (hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetSplitSurplus
        smallBudget cofactorBudget fiberBudget) :
    StrongGoldbach :=
  strongGoldbach_of_minimalCounterexampleFiniteResidueSqrtCofactorPairBudgetSplitSurplus
    smallBudget cofactorBudget
    (minimalCounterexampleFiniteResidueSqrtCofactorPairBudgetSplitSurplus_of_fiberBudgetSplitSurplus
      smallBudget cofactorBudget fiberBudget hsurplus)

/-- Exact pointwise budget for a fixed square-root cofactor fiber. -/
def SqrtCofactorFiberExactBudget (m k : Nat) : Nat :=
  (LargeBadLowerHalfPrimeSqrtCofactorFiber m k).card

/-- Exact summed budget for all fixed square-root cofactor fibers. -/
def SqrtCofactorFiberExactBudgetSum (m : Nat) : Nat :=
  (Finset.Icc 2 (Nat.sqrt m)).sum (SqrtCofactorFiberExactBudget m)

/-- Fully explicit cofactor-fiber budget split using exact small-residue and
exact fiber budgets. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
    (m : Nat) : Prop :=
  LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetSplitSurplus
    m (LowerHalfPrimeSmallResidueClassSqrtExactBudget m)
      (SqrtCofactorFiberExactBudgetSum m) (SqrtCofactorFiberExactBudget m)

/-- The fully explicit cofactor-fiber budget split is exactly the fully
explicit cofactor-pair budget split. -/
theorem sqrtCofactorFiberExactBudgetSplitSurplus_iff_pairExactBudgetSplitSurplus
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
        m ↔
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorPairExactBudgetSplitSurplus
        m := by
  constructor
  · intro hsurplus
    rcases hsurplus with ⟨hsmall, _hpoint, _hsum, hmargin⟩
    refine ⟨hsmall, ?_, ?_⟩
    · unfold SqrtCofactorPairBudgetBound
      exact le_rfl
    · unfold SqrtCofactorPairTwoBudgetMargin
      unfold SqrtCofactorPairTwoBudgetMargin at hmargin
      simpa [SqrtCofactorFiberExactBudgetSum,
        SqrtCofactorFiberExactBudget,
        largeBadLowerHalfPrimeCofactorPairs_card_eq_sum_fibers_at_sqrt] using
        hmargin
  · intro hsurplus
    rcases hsurplus with ⟨hsmall, _hcofactor, hmargin⟩
    refine ⟨hsmall, ?_, ?_, ?_⟩
    · intro k _hk
      unfold SqrtCofactorFiberExactBudget
      exact le_rfl
    · unfold SqrtCofactorFiberPointwiseBudgetSum
      unfold SqrtCofactorFiberExactBudgetSum
      exact le_rfl
    · unfold SqrtCofactorPairTwoBudgetMargin
      unfold SqrtCofactorPairTwoBudgetMargin at hmargin
      simpa [SqrtCofactorFiberExactBudgetSum,
        SqrtCofactorFiberExactBudget,
        largeBadLowerHalfPrimeCofactorPairs_card_eq_sum_fibers_at_sqrt] using
        hmargin

/-- Minimal-counterexample version of the fully explicit cofactor-fiber
budget split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus :
    Prop :=
  ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
      m

/-- The fully explicit cofactor-fiber budget split is exact-strength:
over minimal counterexamples it is equivalent to the current `50000` tail
target. -/
theorem currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus :
    Round1Status.CurrentFormalTarget50000 ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus := by
  constructor
  · intro htarget m hm
    have hpair :
        MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPairExactBudgetSplitSurplus :=
      (currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorPairExactBudgetSplitSurplus).mp
        htarget
    exact
      (sqrtCofactorFiberExactBudgetSplitSurplus_iff_pairExactBudgetSplitSurplus
        m).mpr (hpair m hm)
  · intro hsurplus
    have hpair :
        MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPairExactBudgetSplitSurplus := by
      intro m hm
      exact
        (sqrtCofactorFiberExactBudgetSplitSurplus_iff_pairExactBudgetSplitSurplus
          m).mp (hsurplus m hm)
    exact
      (currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorPairExactBudgetSplitSurplus).mpr
        hpair

/-- The fully explicit cofactor-fiber budget split is also equivalent to the
project headline. -/
theorem strongGoldbach_iff_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus :
    StrongGoldbach ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus := by
  exact
    strongGoldbach_iff_minimalCounterexampleFiniteResidueSqrtCofactorPairExactBudgetSplitSurplus.trans
      ((currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus).symm.trans
        currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorPairExactBudgetSplitSurplus).symm

/-- Component feasibility forced by the fully explicit cofactor-fiber budget
split.  Both the exact small-residue budget and the exact fiber-sum budget
must sit strictly below the lower-half prime count. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentFeasibility
    (m : Nat) : Prop :=
  LowerHalfPrimeSmallResidueClassSqrtExactBudget m <
      Nat.primeCounting (m / 2) ∧
    SqrtCofactorFiberExactBudgetSum m < Nat.primeCounting (m / 2)

/-- Disjunctive component-budget obstruction for the fully explicit
cofactor-fiber budget split. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction
    (m : Nat) : Prop :=
  Nat.primeCounting (m / 2) ≤
      LowerHalfPrimeSmallResidueClassSqrtExactBudget m ∨
    Nat.primeCounting (m / 2) ≤ SqrtCofactorFiberExactBudgetSum m

/-- The exact cofactor-fiber split forces both component budgets to be
individually feasible. -/
theorem sqrtCofactorFiberComponentFeasibility_of_fiberExactBudgetSplitSurplus
    {m : Nat}
    (hsurplus :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentFeasibility
      m := by
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus at hsurplus
  rcases hsurplus with ⟨_hsmall, _hpoint, _hsum, hmargin⟩
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentFeasibility
  unfold SqrtCofactorPairTwoBudgetMargin at hmargin
  constructor <;> omega

/-- The component-budget obstruction is exactly the negation of component
feasibility. -/
theorem sqrtCofactorFiberComponentBudgetObstruction_iff_not_componentFeasibility
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction
        m ↔
      ¬
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentFeasibility
          m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentFeasibility
  constructor
  · intro h hfeasible
    rcases h with hsmall | hfiber <;> omega
  · intro hnot
    by_cases hsmall :
        Nat.primeCounting (m / 2) ≤
          LowerHalfPrimeSmallResidueClassSqrtExactBudget m
    · exact Or.inl hsmall
    · right
      by_contra hfiber
      exact hnot ⟨by omega, by omega⟩

/-- Any component-budget obstruction rules out the fully explicit cofactor-
fiber budget split. -/
theorem not_sqrtCofactorFiberExactBudgetSplitSurplus_of_componentBudgetObstruction
    {m : Nat}
    (hcomponent :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction
        m) :
    ¬
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
        m := by
  intro hsurplus
  have hnot :
      ¬
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentFeasibility
          m :=
    (sqrtCofactorFiberComponentBudgetObstruction_iff_not_componentFeasibility
      m).mp hcomponent
  exact hnot
    (sqrtCofactorFiberComponentFeasibility_of_fiberExactBudgetSplitSurplus
      hsurplus)

/-- Minimal-counterexample package for a component-budget obstruction to the
fully explicit cofactor-fiber split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction :
    Prop :=
  ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction
      m

/-- The minimal-counterexample component obstruction is exactly existence of a
minimal counterexample where component feasibility fails. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorFiberComponentBudgetObstruction_iff_exists_minimalCounterexample_not_componentFeasibility :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction ↔
      ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
        ¬
          LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentFeasibility
            m := by
  constructor
  · rintro ⟨m, hm, hcomponent⟩
    exact
      ⟨m, hm,
        (sqrtCofactorFiberComponentBudgetObstruction_iff_not_componentFeasibility
          m).mp hcomponent⟩
  · rintro ⟨m, hm, hnot⟩
    exact
      ⟨m, hm,
        (sqrtCofactorFiberComponentBudgetObstruction_iff_not_componentFeasibility
          m).mpr hnot⟩

/-- A minimal-counterexample component obstruction rules out the exact
cofactor-fiber split over all minimal counterexamples. -/
theorem not_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus_of_componentBudgetObstruction
    (hbad :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction) :
    ¬
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus := by
  intro hsurplus
  rcases hbad with ⟨m, hm, hcomponent⟩
  exact
    not_sqrtCofactorFiberExactBudgetSplitSurplus_of_componentBudgetObstruction
      hcomponent (hsurplus m hm)

/-- A minimal-counterexample component obstruction is incompatible with the
current `50000` target. -/
theorem not_currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberComponentBudgetObstruction
    (hbad :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction) :
    ¬ Round1Status.CurrentFormalTarget50000 := by
  intro htarget
  have hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus :=
    (currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus).mp
      htarget
  exact
    not_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus_of_componentBudgetObstruction
      hbad hsurplus

/-- A minimal-counterexample component obstruction is incompatible with the
explicit lower-bound tail target. -/
theorem not_explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberComponentBudgetObstruction
    (hbad :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction) :
    ¬ ExplicitGoldbachLowerBound 50000 := by
  intro htarget
  exact
    not_currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberComponentBudgetObstruction
      hbad (by simpa [Round1Status.CurrentFormalTarget50000] using htarget)

/-- A minimal-counterexample component obstruction is incompatible with the
project headline. -/
theorem not_strongGoldbach_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberComponentBudgetObstruction
    (hbad :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction) :
    ¬ StrongGoldbach := by
  intro hgoldbach
  have hsurplus :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus :=
    (strongGoldbach_iff_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus).mp
      hgoldbach
  exact
    not_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus_of_componentBudgetObstruction
      hbad hsurplus

/-- Exact total-budget obstruction to the fully explicit cofactor-fiber split:
the exact small-residue budget and the exact fiber-sum budget together already
reach the available lower-half prime count. -/
def LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
    (m : Nat) : Prop :=
  Nat.primeCounting (m / 2) ≤
    LowerHalfPrimeSmallResidueClassSqrtExactBudget m +
      SqrtCofactorFiberExactBudgetSum m

/-- The exact cofactor-fiber total-budget obstruction is exactly the negation
of the fully explicit cofactor-fiber split. -/
theorem sqrtCofactorFiberBudgetObstruction_iff_not_splitSurplus
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
        m ↔
      ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
        m := by
  constructor
  · intro hbudget hsurplus
    unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction at hbudget
    unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus at hsurplus
    rcases hsurplus with ⟨_hsmall, _hpoint, _hsum, hmargin⟩
    unfold SqrtCofactorPairTwoBudgetMargin at hmargin
    omega
  · intro hnot
    unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
    by_contra hbudget
    exact hnot (by
      unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
      refine ⟨
        lowerHalfPrimeSmallResidueClassSqrtBudget_exactBudget m,
        ?_,
        ?_,
        ?_⟩
      · intro k _hk
        unfold SqrtCofactorFiberExactBudget
        exact le_rfl
      · unfold SqrtCofactorFiberPointwiseBudgetSum
        unfold SqrtCofactorFiberExactBudgetSum
        exact le_rfl
      · unfold SqrtCofactorPairTwoBudgetMargin
        omega)

/-- Component-budget failure is a special case of exact total-budget
obstruction for the cofactor-fiber split. -/
theorem sqrtCofactorFiberBudgetObstruction_of_componentBudgetObstruction
    {m : Nat}
    (hcomponent :
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction
        m) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
      m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction at *
  rcases hcomponent with hsmall | hfiber <;> omega

/-- Minimal-counterexample package for exact total-budget obstruction to the
fully explicit cofactor-fiber split. -/
def MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction :
    Prop :=
  ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
      m

/-- Component-budget obstruction lifts into exact total-budget obstruction at
the minimal-counterexample layer. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_of_componentBudgetObstruction
    (hbad :
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberComponentBudgetObstruction) :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction := by
  rcases hbad with ⟨m, hm, hcomponent⟩
  exact
    ⟨m, hm,
      sqrtCofactorFiberBudgetObstruction_of_componentBudgetObstruction
        hcomponent⟩

/-- Exact total-budget obstruction is precisely the failure of the
exact-strength cofactor-fiber handoff over minimal counterexamples. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_splitSurplus :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction ↔
      ¬
        MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus := by
  constructor
  · rintro ⟨m, hm, hbudget⟩ hsurplus
    exact
      (sqrtCofactorFiberBudgetObstruction_iff_not_splitSurplus
        m).mp hbudget (hsurplus m hm)
  · intro hnot
    classical
    have hnot_exists :
        ∃ m : Nat,
          ¬ (MinimalBinaryGoldbachCounterexample m →
            LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
              m) :=
      not_forall.mp hnot
    rcases hnot_exists with ⟨m, hmnot⟩
    have hm : MinimalBinaryGoldbachCounterexample m := by
      by_contra hminimal
      exact hmnot (fun h => False.elim (hminimal h))
    have hnotSurplus :
        ¬
          LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
            m := by
      intro hsurplus
      exact hmnot (fun _ => hsurplus)
    exact
      ⟨m, hm,
        (sqrtCofactorFiberBudgetObstruction_iff_not_splitSurplus
          m).mpr hnotSurplus⟩

/-- The exact cofactor-fiber total-budget obstruction is equivalent to failure
of the current `50000` status-layer target. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_currentFormalTarget50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction ↔
      ¬ Round1Status.CurrentFormalTarget50000 := by
  constructor
  · intro hbudget htarget
    have hsurplus :
        MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus :=
      (currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus).mp
        htarget
    exact
      (minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_splitSurplus).mp
        hbudget hsurplus
  · intro hnotTarget
    have hnotSurplus :
        ¬
          MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus := by
      intro hsurplus
      exact hnotTarget
        ((currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus).mpr
          hsurplus)
    exact
      (minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_splitSurplus).mpr
        hnotSurplus

/-- The exact cofactor-fiber total-budget obstruction is equivalent to failure
of the literal remaining `ExplicitGoldbachLowerBound 50000` target. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_explicitLowerBound50000 :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction ↔
      ¬ ExplicitGoldbachLowerBound 50000 := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_currentFormalTarget50000

/-- Positive form of the exact cofactor-fiber total-budget criterion. -/
theorem explicitLowerBound50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction :
    ExplicitGoldbachLowerBound 50000 ↔
      ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction := by
  constructor
  · intro htarget hbudget
    exact
      (minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_explicitLowerBound50000).mp
        hbudget htarget
  · intro hnotBudget
    by_contra htarget
    exact hnotBudget
      ((minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_explicitLowerBound50000).mpr
        htarget)

/-- Positive status-layer form of the exact cofactor-fiber total-budget
criterion. -/
theorem currentFormalTarget50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction :
    Round1Status.CurrentFormalTarget50000 ↔
      ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction := by
  simpa [Round1Status.CurrentFormalTarget50000] using
    explicitLowerBound50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction

/-- The exact cofactor-fiber total-budget obstruction is equivalent to failure
of the project headline. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_strongGoldbach :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction ↔
      ¬ StrongGoldbach := by
  constructor
  · intro hbudget hgoldbach
    have hsurplus :
        MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus :=
      (strongGoldbach_iff_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus).mp
        hgoldbach
    exact
      (minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_splitSurplus).mp
        hbudget hsurplus
  · intro hnotGoldbach
    have hnotSurplus :
        ¬
          MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus := by
      intro hsurplus
      exact hnotGoldbach
        ((strongGoldbach_iff_minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus).mpr
          hsurplus)
    exact
      (minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_splitSurplus).mpr
        hnotSurplus

/-- Positive headline form of the exact cofactor-fiber total-budget
criterion. -/
theorem strongGoldbach_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction :
    StrongGoldbach ↔
      ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction := by
  constructor
  · intro hgoldbach hbudget
    exact
      (minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_strongGoldbach).mp
        hbudget hgoldbach
  · intro hnotBudget
    by_contra hgoldbach
    exact hnotBudget
      ((minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_strongGoldbach).mpr
        hgoldbach)

/-- Absence of a minimal-counterexample total-budget obstruction is the same
as pointwise absence of the local obstruction on every minimal counterexample. -/
theorem not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_forall_minimal_not_budgetObstruction :
    ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction ↔
      ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
        ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
          m := by
  constructor
  · intro hnot m hm hbudget
    exact hnot ⟨m, hm, hbudget⟩
  · intro hall hbudget
    rcases hbudget with ⟨m, hm, hlocal⟩
    exact hall m hm hlocal

/-- The exact cofactor-fiber total-budget obstruction is absent exactly when
the corresponding explicit strict budget inequality holds. -/
theorem not_sqrtCofactorFiberBudgetObstruction_iff_budgetStrict
    (m : Nat) :
    ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
        m ↔
      LowerHalfPrimeSmallResidueClassSqrtExactBudget m +
          SqrtCofactorFiberExactBudgetSum m <
        Nat.primeCounting (m / 2) := by
  unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
  omega

/-- The fully explicit cofactor-fiber split is exactly the strict two-budget
inequality for the exact small-residue and exact fiber-sum budgets. -/
theorem sqrtCofactorFiberExactBudgetSplitSurplus_iff_budgetStrict
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
        m ↔
      LowerHalfPrimeSmallResidueClassSqrtExactBudget m +
          SqrtCofactorFiberExactBudgetSum m <
        Nat.primeCounting (m / 2) := by
  constructor
  · intro hsurplus
    unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus at hsurplus
    rcases hsurplus with ⟨_hsmall, _hpoint, _hsum, hmargin⟩
    unfold SqrtCofactorPairTwoBudgetMargin at hmargin
    exact hmargin
  · intro hstrict
    unfold LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
    refine ⟨
      lowerHalfPrimeSmallResidueClassSqrtBudget_exactBudget m,
      ?_,
      ?_,
      ?_⟩
    · intro k _hk
      unfold SqrtCofactorFiberExactBudget
      exact le_rfl
    · unfold SqrtCofactorFiberPointwiseBudgetSum
      unfold SqrtCofactorFiberExactBudgetSum
      exact le_rfl
    · unfold SqrtCofactorPairTwoBudgetMargin
      exact hstrict

/-- The strict exact cofactor-fiber budget inequality is the same local
fiber-sum criterion introduced before the explicit-budget packaging. -/
theorem sqrtCofactorFiberBudgetStrict_iff_fiberSplitSurplus
    (m : Nat) :
    (LowerHalfPrimeSmallResidueClassSqrtExactBudget m +
          SqrtCofactorFiberExactBudgetSum m <
        Nat.primeCounting (m / 2)) ↔
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus
        m := by
  unfold
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus
    LowerHalfPrimeSmallResidueClassSqrtExactBudget
    SqrtCofactorFiberExactBudgetSum
    SqrtCofactorFiberExactBudget
  rw [lowerHalfPrimes_card_eq_primeCounting_half]

/-- The fully explicit cofactor-fiber split is exactly the earlier local
fiber-sum cardinality criterion. -/
theorem sqrtCofactorFiberExactBudgetSplitSurplus_iff_fiberSplitSurplus
    (m : Nat) :
    LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus
        m ↔
      LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus
        m :=
  (sqrtCofactorFiberExactBudgetSplitSurplus_iff_budgetStrict m).trans
    (sqrtCofactorFiberBudgetStrict_iff_fiberSplitSurplus m)

/-- Minimal-counterexample exact-budget and fiber-sum packages are the same
square-root cofactor-fiber obligation. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus_iff_sqrtCofactorFiberSplitSurplus :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus ↔
      MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus := by
  constructor
  · intro hsurplus m hm
    exact
      (sqrtCofactorFiberExactBudgetSplitSurplus_iff_fiberSplitSurplus
        m).mp (hsurplus m hm)
  · intro hsurplus m hm
    exact
      (sqrtCofactorFiberExactBudgetSplitSurplus_iff_fiberSplitSurplus
        m).mpr (hsurplus m hm)

/-- Minimal-counterexample exact cofactor-fiber split is exactly the pointwise
strict exact cofactor-fiber budget inequality on every minimal counterexample. -/
theorem minimalCounterexampleFiniteResidueSqrtCofactorFiberExactBudgetSplitSurplus_iff_forall_minimal_budgetStrict :
    MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberExactBudgetSplitSurplus ↔
      ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
        LowerHalfPrimeSmallResidueClassSqrtExactBudget m +
            SqrtCofactorFiberExactBudgetSum m <
          Nat.primeCounting (m / 2) := by
  constructor
  · intro hsurplus m hm
    exact
      (sqrtCofactorFiberExactBudgetSplitSurplus_iff_budgetStrict
        m).mp (hsurplus m hm)
  · intro hstrict m hm
    exact
      (sqrtCofactorFiberExactBudgetSplitSurplus_iff_budgetStrict
        m).mpr (hstrict m hm)

/-- Current target as a pointwise strict exact cofactor-fiber budget condition
on every minimal counterexample. -/
theorem currentFormalTarget50000_iff_forall_minimalCounterexample_sqrtCofactorFiberBudgetStrict :
    Round1Status.CurrentFormalTarget50000 ↔
      ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
        LowerHalfPrimeSmallResidueClassSqrtExactBudget m +
            SqrtCofactorFiberExactBudgetSum m <
          Nat.primeCounting (m / 2) := by
  constructor
  · intro htarget m hm
    have hnotBudget :
        ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction :=
      (currentFormalTarget50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction).mp
        htarget
    have hlocal :
        ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
          m :=
      (not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_forall_minimal_not_budgetObstruction).mp
        hnotBudget m hm
    exact
      (not_sqrtCofactorFiberBudgetObstruction_iff_budgetStrict
        m).mp hlocal
  · intro hstrict
    exact
      (currentFormalTarget50000_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction).mpr
        (by
          exact
            (not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_forall_minimal_not_budgetObstruction).mpr
              (fun m hm =>
                (not_sqrtCofactorFiberBudgetObstruction_iff_budgetStrict
                  m).mpr (hstrict m hm)))

/-- Headline statement as a pointwise strict exact cofactor-fiber budget
condition on every minimal counterexample. -/
theorem strongGoldbach_iff_forall_minimalCounterexample_sqrtCofactorFiberBudgetStrict :
    StrongGoldbach ↔
      ∀ m : Nat, MinimalBinaryGoldbachCounterexample m →
        LowerHalfPrimeSmallResidueClassSqrtExactBudget m +
            SqrtCofactorFiberExactBudgetSum m <
          Nat.primeCounting (m / 2) := by
  constructor
  · intro hgoldbach m hm
    have hnotBudget :
        ¬ MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction :=
      (strongGoldbach_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction).mp
        hgoldbach
    have hlocal :
        ¬ LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
          m :=
      (not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_forall_minimal_not_budgetObstruction).mp
        hnotBudget m hm
    exact
      (not_sqrtCofactorFiberBudgetObstruction_iff_budgetStrict
        m).mp hlocal
  · intro hstrict
    exact
      (strongGoldbach_iff_not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction).mpr
        (by
          exact
            (not_minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_forall_minimal_not_budgetObstruction).mpr
              (fun m hm =>
                (not_sqrtCofactorFiberBudgetObstruction_iff_budgetStrict
                  m).mpr (hstrict m hm)))

/-- Negated headline form: failure of `StrongGoldbach` is equivalent to
existence of a minimal counterexample satisfying the exact cofactor-fiber
total-budget obstruction. -/
theorem not_strongGoldbach_iff_exists_minimalCounterexample_sqrtCofactorFiberBudgetObstruction :
    ¬ StrongGoldbach ↔
      ∃ m : Nat, MinimalBinaryGoldbachCounterexample m ∧
        LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction
          m := by
  simpa [MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorFiberBudgetObstruction] using
    minimalCounterexampleFiniteResidueSqrtCofactorFiberBudgetObstruction_iff_not_strongGoldbach.symm

end CounterexampleReduction
end Gdbh
