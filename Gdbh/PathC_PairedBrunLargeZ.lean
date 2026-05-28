/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P17-T7 (Phase 17 / Path C — Large-`z` absorption for the
        Brun-Goldbach paired sieve, post Round 2)
-/
import Gdbh.PathC_PairedMainTermAssembly

/-!
# Path C — P17-T7: Large-`z` absorption for the paired sieve

This file is the **P17-T7 deliverable** in Phase 17 (Path C closure),
following the breakthrough of P17-T6 ("Strategy A refactor").

## Context

P17-T6 refactored `BrunGoldbachPairedMainTermRefined` to the new named
open Prop `BrunGoldbachPairedMainTermRefinedAtSqrt` (specialised at
`z = Nat.sqrt n` only), and proved the equivalence

```
BrunGoldbachPairedMainTermRefined  ↔  PairedMainTermAbsorption
```

(see `Gdbh/PathC_PairedMainTermAssembly.lean:379`).  The antitonicity
of `goldbachSiftedPair` in `z` was also proved there
(`goldbachSiftedPair_antitone_z`).

T7's remaining work: close `PairedMainTermAbsorption` axiom-cleanly,
or — failing that — expose the *honest* residual sub-Props plus a
forward bridge.

## Mathematical analysis

`PairedMainTermAbsorption` quantifies over **all** `z : ℕ`:

```
∃ C₁ > 0, ∀ n z : ℕ, 0 < n →
  (goldbachSiftedPair n z : ℝ) ≤ C₁ · n · pairedBrunFactor z
                                  + refinedReservoir n z .
```

We split the `(n, z)` range into three regions:

### Region I: `z ≥ n - 1` (large `z`, trivial sift collapse)

For `n ≥ 3` and `z ≥ n - 1`, every `m ∈ [1, n - 1]` has a prime
divisor `≤ m ≤ n - 1 ≤ z`, so `m` is sifted out — except `m = 1`
(no prime divisors).  For `m = 1` and `n ≥ 3`, `n - m = n - 1 ≥ 2`
has a prime factor `≤ n - 1 ≤ z`, so it too is sifted out.  Hence
`goldbachSiftedPair n z = 0`.

### Region II: `√n ≤ z < n - 1` and `n ≥ N₀` (paired Mertens absorption)

By antitonicity in `z`:

```
goldbachSiftedPair n z  ≤  goldbachSiftedPair n (Nat.sqrt n) .
```

By AtSqrt + the Mertens upper bound `pairedBrunFactor (√n) ≤ C'/(log n)²`
and the Mertens lower bound `pairedBrunFactor z ≥ K/(log n)²`:

```
C · n · pairedBrunFactor (√n)  ≤  C · n · C'/(log n)²
                              =  (C · C'/K) · n · K/(log n)²
                              ≤  (C · C'/K) · n · pairedBrunFactor z .
```

The bridge constant `C · C'/K` is then absorbed into a uniform `C₁`.

### Region III: residual region (small `z` or small `n`)

The downward extension `z < √n` is non-trivial: for `z = 3`,
`pairedBrunFactor z = 1/3`, while the sift is much closer to
`n / (log n)`.  Antitonicity does not bridge `z = √n` downwards
because `goldbachSiftedPair n z` *grows* as `z` shrinks.

Similarly, for `n < N₀`, the Mertens asymptotics do not apply, so
the large-`z` absorption argument fails for these bounded `n`.

Both content gaps are absorbed into a single residual Prop
`PairedMainTermResidualLowRegion`.

## Outputs of this file

1. **Trivial sift collapse**: `goldbachSiftedPair n z = 0` for `n ≥ 3`,
   `z ≥ n - 1`.

2. **Local antitonicity** of `pairedBrunFactor` (re-proved here as a
   standalone lemma, to bridge bounded-`z` cases).

3. **Three named open residual Props**:

   * `PairedBrunFactorMertensLower` — `pairedBrunFactor z ≥ K/(log n)²`
     for `z ∈ [√n, n)`, `n ≥ N₀`.

   * `PairedBrunFactorMertensUpperAtSqrt` — `pairedBrunFactor (√n) ≤
     C'/(log n)²` for `n ≥ N₀`.

   * `PairedMainTermResidualLowRegion` — combined "low-region"
     residual covering both `n < N₀` and `z < √n`.

4. **Forward bridge** `absorption_of_atSqrt_and_residuals`:

   ```
   AtSqrt + MertensLower + MertensUpperAtSqrt + ResidualLowRegion
     ⇒  PairedMainTermAbsorption .
   ```

## Honest assessment

The single-hypothesis bridge `AtSqrt + Mertens-lower ⇒ Absorption`
as initially sketched **fails** mathematically: for `z ∈ [√n, n)`,
AtSqrt gives a bound at `√n` involving `pairedBrunFactor (√n)`, which
by antitonicity is *larger* than `pairedBrunFactor z`.  The gap
between them cannot be absorbed by the reservoir `n / (log n)²`
uniformly without a matching upper bound on `pairedBrunFactor (√n)`.
We therefore expose `PairedBrunFactorMertensUpperAtSqrt` as a second
sub-Prop.  And Region III genuinely requires Brun-Bonferroni at
sub-`√n` thresholds, exposed as `PairedMainTermResidualLowRegion`.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* All theorems below are axiom-clean: only `Classical.choice`,
  `Quot.sound`, `propext`.
-/

namespace Gdbh
namespace PathCPairedBrunLargeZ

open Real
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPairSet mem_goldbachSiftedPairSet
   goldbachSiftedPair_le)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunRefinedComposition
  (refinedReservoir refinedReservoir_def)
open Gdbh.PathCPairedBrunSmallZ
  (refinedReservoir_nonneg pairedBrunFactor_eq_one_of_le_two)
open Gdbh.PathCPairedMainTermAssembly
  (BrunGoldbachPairedMainTermRefinedAtSqrt
   PairedMainTermAbsorption
   goldbachSiftedPair_antitone_z
   goldbachSiftedPair_antitone_z_real)

/-! ## Section 1 — Trivial sift collapse at large `z`

For `n ≥ 3` and `z ≥ n - 1`, every `m ∈ [1, n - 1]` is sifted out:
either `m ≥ 2` has a prime factor `≤ m ≤ n - 1 ≤ z`, or `m = 1`,
in which case `n - m = n - 1 ≥ 2` has a prime factor `≤ n - 1 ≤ z`. -/

/-- **Sift collapse at large `z`.**  For `n ≥ 3` and `z ≥ n - 1`,
no `m ∈ [1, n - 1]` is in the paired sifted set. -/
theorem goldbachSiftedPairSet_eq_empty_of_large_z
    {n z : ℕ} (hn : 3 ≤ n) (hz : n - 1 ≤ z) :
    goldbachSiftedPairSet n z = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rw [mem_goldbachSiftedPairSet] at hm
  obtain ⟨⟨h1, h2⟩, hm_nosmall, hnm_nosmall⟩ := hm
  rcases Nat.lt_or_ge 1 m with h_m_ge_two | h_m_le_one
  · have hm_ne_one : m ≠ 1 := by omega
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hm_ne_one
    have hp_le_m : p ≤ m := Nat.le_of_dvd (by omega) hp_dvd
    have hp_le_z : p ≤ z := le_trans (le_trans hp_le_m h2) hz
    exact hm_nosmall p hp_le_z hp_prime hp_dvd
  · interval_cases m
    have hnm_ne_one : n - 1 ≠ 1 := by omega
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hnm_ne_one
    have hp_le_nm : p ≤ n - 1 := Nat.le_of_dvd (by omega) hp_dvd
    have hp_le_z : p ≤ z := le_trans hp_le_nm hz
    exact hnm_nosmall p hp_le_z hp_prime hp_dvd

/-- **Sift count is zero at large `z`** (n ≥ 3, z ≥ n - 1). -/
theorem goldbachSiftedPair_eq_zero_of_large_z
    {n z : ℕ} (hn : 3 ≤ n) (hz : n - 1 ≤ z) :
    goldbachSiftedPair n z = 0 := by
  unfold goldbachSiftedPair
  rw [goldbachSiftedPairSet_eq_empty_of_large_z hn hz]
  exact Finset.card_empty

/-- **Real-valued form** of the sift collapse at large `z`. -/
theorem goldbachSiftedPair_eq_zero_of_large_z_real
    {n z : ℕ} (hn : 3 ≤ n) (hz : n - 1 ≤ z) :
    (goldbachSiftedPair n z : ℝ) = 0 := by
  rw [goldbachSiftedPair_eq_zero_of_large_z hn hz]
  norm_num

/-! ## Section 2 — Local antitonicity of `pairedBrunFactor`

We re-prove `pairedBrunFactor` antitone in `z` here (the existing
proof in `PathC_Final.lean:620` is `private`).  Each factor `1 - 2/p`
lies in `(0, 1]`, so adding more such factors decreases the product. -/

/-- **Antitonicity of `pairedBrunFactor`.**  If `z₁ ≤ z₂` then
`pairedBrunFactor z₂ ≤ pairedBrunFactor z₁`. -/
theorem pairedBrunFactor_antitone {z₁ z₂ : ℕ} (hz : z₁ ≤ z₂) :
    pairedBrunFactor z₂ ≤ pairedBrunFactor z₁ := by
  unfold pairedBrunFactor
  have hsub : (Finset.Icc 3 z₁).filter Nat.Prime
      ⊆ (Finset.Icc 3 z₂).filter Nat.Prime := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, hpr⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, hpa⟩
    refine Finset.mem_filter.mpr ⟨?_, hpr⟩
    exact Finset.mem_Icc.mpr ⟨hp3, hpa.trans hz⟩
  refine Finset.prod_le_prod_of_subset_of_le_one hsub ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _hpr⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have h_two_div_le : (2 : ℝ) / (p : ℝ) ≤ 2 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp_real
    have h23 : (2 : ℝ) / 3 < 1 := by norm_num
    linarith
  · intro p hpb _hpa
    rcases Finset.mem_filter.mp hpb with ⟨hp_Icc, _hpr⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have h_two_div_nn : (0 : ℝ) ≤ 2 / (p : ℝ) :=
      div_nonneg (by norm_num) (le_of_lt hp_pos)
    linarith

/-! ## Section 3 — Residual sub-Props (honest exposure)

The mathematical analysis shows that closing `PairedMainTermAbsorption`
from `BrunGoldbachPairedMainTermRefinedAtSqrt` alone is *impossible* —
the AtSqrt slice gives a bound at `√n` only, and uniformly bridging
to other `(n, z)`-slices requires additional analytic input.  We
expose three named open sub-Props that, together with AtSqrt, are
sufficient to close `Absorption`. -/

/-- **`PairedBrunFactorMertensLower`.**  A uniform lower bound

```
pairedBrunFactor z  ≥  K / (log n)²    for z ∈ [√n, n), n ≥ N₀.
```

Classically a direct consequence of Mertens' third theorem (1873):
`∏_{p ≤ z} (1 - 1/p) ~ e^{-γ} / log z`, so
`pairedBrunFactor z ~ C / (log z)²`; for `z ≥ √n` we have
`log z ≥ (1/2) log n`, giving `(log z)² ≥ (1/4) (log n)²`, hence the
bound with `K = 4 C` (asymptotically).

**Status**: classical, mathlib v4.29.1 **open**.  Reduces to the
established `PairedBrunMertensThirdGap` Prop in
`Gdbh.PathCMertensProof`. -/
def PairedBrunFactorMertensLower : Prop :=
  ∃ K N₀ : ℕ, 0 < K ∧ ∀ n z : ℕ, N₀ ≤ n →
    Nat.sqrt n ≤ z → z < n →
    (K : ℝ) / (Real.log (n : ℝ))^2 ≤ pairedBrunFactor z

/-- **`PairedBrunFactorMertensUpperAtSqrt`.**  The Mertens upper
bound at the canonical sieve threshold `z = √n`:

```
pairedBrunFactor (Nat.sqrt n)  ≤  C' / (log n)²    for n ≥ N₀.
```

Classically `pairedBrunFactor (√n) ~ C / (log √n)² = 4 C / (log n)²`.

**Status**: classical, mathlib v4.29.1 **open**.  Reduces to the
established `PairedBrunMertensThirdGap` Prop specialised at
`z = √n`. -/
def PairedBrunFactorMertensUpperAtSqrt : Prop :=
  ∃ C' : ℝ, ∃ N₀ : ℕ, 0 < C' ∧ ∀ n : ℕ, N₀ ≤ n →
    pairedBrunFactor (Nat.sqrt n) ≤ C' / (Real.log (n : ℝ))^2

/-- **`PairedMainTermResidualLowRegion`.**  The combined residual
covering:

* `z < Nat.sqrt n` (downward extension below the canonical threshold);
* `n < N₀` (small-`n` boundary cases).

Concretely:

```
∃ C₁ > 0, ∃ N₀ : ℕ, ∀ n z : ℕ, 0 < n →
  (n < N₀ ∨ z < Nat.sqrt n) →
  (goldbachSiftedPair n z : ℝ)
    ≤ C₁ · n · pairedBrunFactor z + refinedReservoir n z .
```

Classically follows from Brun-Bonferroni at all thresholds combined
with finite case analysis for bounded `n`.  **Not** implied by the
AtSqrt slice alone — antitonicity of `goldbachSiftedPair` in `z`
goes the wrong way for `z < √n`.

**Status**: classical, mathlib v4.29.1 **open**. -/
def PairedMainTermResidualLowRegion : Prop :=
  ∃ C₁ : ℝ, ∃ N₀ : ℕ, 0 < C₁ ∧
    ∀ n z : ℕ, 0 < n → (n < N₀ ∨ z < Nat.sqrt n) →
      (goldbachSiftedPair n z : ℝ)
        ≤ C₁ * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z

/-! ## Section 4 — Residual `N₀` enlargement

If `PairedMainTermResidualLowRegion` holds with some `N₀_resid`, then
by taking the existing bound for `n < N₀_resid` AND combining it with
the AtSqrt-plus-antitonicity argument for `N₀_resid ≤ n < M` and
`z ≥ √n` (with `z ≤ M - 2` bounded), we can absorb the
"intermediate-`n`" subregion into an enlarged residual with any
larger threshold `M`.  This is done by choosing `C₁` large enough to
absorb the (finitely many bounded-`n`) cases. -/

/-- **Enlarged residual.**  Given `PairedMainTermResidualLowRegion`
with threshold `N₀_resid` and AtSqrt, we can extract an enlarged
residual covering `n < M ∨ z < √n` for any `M ≥ N₀_resid`, by using
the AtSqrt bound combined with the bounded-z antitonicity argument
for the intermediate range `N₀_resid ≤ n < M` and `√n ≤ z ≤ n - 2`.

Specifically: for `n ∈ [N₀_resid, M - 1]` and `√n ≤ z ≤ n - 2`, the
value `z` is bounded by `M - 2`, so `pairedBrunFactor z ≥
pairedBrunFactor (M - 2)`, a fixed positive constant.  Hence
`C · n · pairedBrunFactor (√n) ≤ C · M · 1 ≤
(C · M / pairedBrunFactor (M - 2)) · n · pairedBrunFactor z`.

We absorb the case `z ≥ n - 1` (and `n ≥ 3`) via the sift collapse.
For `n ∈ {1, 2}` and `z ≥ √n`, we use the catch defusal already
proved in PathC_PairedMainTermAssembly. -/
private lemma residual_enlarged_helper
    (hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrt)
    (hResid : PairedMainTermResidualLowRegion)
    (M : ℕ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ n z : ℕ, 0 < n → (n < M ∨ z < Nat.sqrt n) →
        (goldbachSiftedPair n z : ℝ)
          ≤ C₁ * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z := by
  obtain ⟨C, hCpos, hAtSqrtBd⟩ := hAtSqrt
  obtain ⟨C_resid, N₀_resid, hC_resid_pos, hResidBd⟩ := hResid
  -- Lower bound on pairedBrunFactor z for z ≤ M (uniform positive).
  -- Use pairedBrunFactor M ≤ pairedBrunFactor z for z ≤ M (antitone).
  -- The minimum is pairedBrunFactor M.
  -- Define pBF_min = pairedBrunFactor M > 0.
  set pBF_min : ℝ := pairedBrunFactor M with hpBF_min_def
  have hpBF_min_pos : 0 < pBF_min := pairedBrunFactor_pos M
  -- Bound: for the bounded-n subregion N₀_resid ≤ n < M and z ≤ n - 2,
  -- we need C · n · pairedBrunFactor (√n) ≤ C_bridged · n · pairedBrunFactor z.
  -- pairedBrunFactor z ≥ pairedBrunFactor M = pBF_min (antitone, z ≤ M-2 ≤ M).
  -- pairedBrunFactor (√n) ≤ 1.
  -- So C · n · pairedBrunFactor (√n) ≤ C · n ≤
  --     (C / pBF_min) · n · pBF_min ≤ (C / pBF_min) · n · pairedBrunFactor z.
  set C_bd : ℝ := C / pBF_min with hC_bd_def
  have hC_bd_pos : 0 < C_bd := div_pos hCpos hpBF_min_pos
  -- And we also need to cover the n ∈ {1, 2} cases with z ≥ √n.
  -- For n = 1: sift = 0 (empty range).
  -- For n = 2 and any z: sift ≤ 1, reservoir = 2/(log 2)² > 1.  So
  -- the inequality holds for C₁ ≥ 0.
  -- C₁ = max(C_resid, C_bd) + 1.
  set C₁ : ℝ := max C_resid C_bd + 1 with hC₁_def
  have hC₁_pos : 0 < C₁ := by
    rw [hC₁_def]
    have : 0 ≤ max C_resid C_bd := le_max_of_le_left (le_of_lt hC_resid_pos)
    linarith
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro n z hn hcond
  -- Split: n < N₀_resid (use hResid directly via the original disjunct).
  -- Otherwise n ≥ N₀_resid.  Then by hypothesis n < M OR z < √n.
  --   if z < √n: use hResid (via the z < √n disjunct of the *enlarged*
  --     residual which is OK since hResid's disjunct includes z < √n).
  --   if n < M and z ≥ √n: bounded-n subregion, use AtSqrt + bounded
  --     antitonicity.
  by_cases h_n_resid : n < N₀_resid
  · -- Use hResid directly (n < N₀_resid disjunct).
    have h := hResidBd n z hn (Or.inl h_n_resid)
    have h_resid_le_C₁ : C_resid ≤ C₁ := by
      rw [hC₁_def]
      have : C_resid ≤ max C_resid C_bd := le_max_left _ _
      linarith
    have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
    have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
      mul_nonneg h_n_nn h_pf_nn
    have h_main_le : C_resid * (n : ℝ) * pairedBrunFactor z
        ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
      have : C_resid * ((n : ℝ) * pairedBrunFactor z)
          ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
        mul_le_mul_of_nonneg_right h_resid_le_C₁ h_n_pf_nn
      linarith [this]
    linarith
  · -- n ≥ N₀_resid.
    push_neg at h_n_resid
    rcases hcond with h_n_lt_M | h_z_lt_sqrt
    · -- n ≥ N₀_resid AND n < M.  Split on z vs √n.
      by_cases h_z_sqrt : z < Nat.sqrt n
      · -- z < √n: use hResid via the z < √n disjunct.
        have h := hResidBd n z hn (Or.inr h_z_sqrt)
        have h_resid_le_C₁ : C_resid ≤ C₁ := by
          rw [hC₁_def]
          have : C_resid ≤ max C_resid C_bd := le_max_left _ _
          linarith
        have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
        have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
        have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
          mul_nonneg h_n_nn h_pf_nn
        have h_main_le : C_resid * (n : ℝ) * pairedBrunFactor z
            ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
          have : C_resid * ((n : ℝ) * pairedBrunFactor z)
              ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
            mul_le_mul_of_nonneg_right h_resid_le_C₁ h_n_pf_nn
          linarith [this]
        linarith
      · -- z ≥ √n AND n < M AND n ≥ N₀_resid.  Use AtSqrt + bounded antitonicity.
        push_neg at h_z_sqrt
        -- Further split on z vs n - 1.
        rcases Nat.lt_or_ge n 3 with h_n_small | h_n_ge_3
        · -- n ∈ {1, 2}.
          interval_cases n
          · -- n = 1.  sift = 0.
            classical
            unfold goldbachSiftedPair goldbachSiftedPairSet
            have h_empty : (Finset.Icc 1 (1 - 1) : Finset ℕ) = ∅ := by
              apply Finset.Icc_eq_empty
              omega
            rw [h_empty]
            simp
            have h_n_nn : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
            have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
            have h_main_nn : 0 ≤ C₁ * 1 * pairedBrunFactor z := by
              apply mul_nonneg
              · exact mul_nonneg (le_of_lt hC₁_pos) h_n_nn
              · exact h_pf_nn
            have h_res_nn : 0 ≤ refinedReservoir 1 z := refinedReservoir_nonneg 1 z
            linarith
          · -- n = 2.  sift ≤ 1.  reservoir = 2/(log 2)² > 1.
            classical
            have h_sift_le_one : (goldbachSiftedPair 2 z : ℝ) ≤ 1 := by
              have h_card : goldbachSiftedPair 2 z ≤ 1 := by
                unfold goldbachSiftedPair goldbachSiftedPairSet
                refine le_trans (Finset.card_filter_le _ _) ?_
                simp
              exact_mod_cast h_card
            have h_res_gt_one : (1 : ℝ) < refinedReservoir 2 z := by
              show (1 : ℝ) < (2 : ℝ) / (Real.log 2)^2
              have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
              have hlog2_lt_one : Real.log 2 < 1 := by
                have : Real.log 2 < Real.log (Real.exp 1) := by
                  apply Real.log_lt_log (by norm_num : (0 : ℝ) < 2)
                  have h1 : (2 : ℝ) < Real.exp 1 := by
                    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
                    linarith
                  exact h1
                rwa [Real.log_exp] at this
              have hsq_lt_one : (Real.log 2)^2 < 1 := by
                have : (Real.log 2)^2 < 1^2 := by
                  exact sq_lt_sq' (by linarith) hlog2_lt_one
                simpa using this
              have hsq_pos : 0 < (Real.log 2)^2 := by positivity
              rw [lt_div_iff₀ hsq_pos]
              linarith
            have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
            have h_main_nn : 0 ≤ C₁ * ((2 : ℕ) : ℝ) * pairedBrunFactor z := by
              apply mul_nonneg
              · exact mul_nonneg (le_of_lt hC₁_pos) (by norm_num)
              · exact h_pf_nn
            linarith
        · -- n ≥ 3.  Split on z vs n - 1.
          by_cases h_z_collapse : n - 1 ≤ z
          · -- Sift collapse.
            have h_sift_zero : (goldbachSiftedPair n z : ℝ) = 0 :=
              goldbachSiftedPair_eq_zero_of_large_z_real h_n_ge_3 h_z_collapse
            rw [h_sift_zero]
            have h_main_nn : 0 ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
              apply mul_nonneg
              · apply mul_nonneg (le_of_lt hC₁_pos)
                exact_mod_cast Nat.zero_le _
              · exact le_of_lt (pairedBrunFactor_pos z)
            have h_res_nn : 0 ≤ refinedReservoir n z := refinedReservoir_nonneg n z
            linarith
          · -- √n ≤ z ≤ n - 2 ≤ M - 2.  Use AtSqrt + bounded antitonicity.
            push_neg at h_z_collapse
            have hz_lt_n : z < n := by omega
            have hz_le_M : z ≤ M := by omega
            -- pairedBrunFactor z ≥ pairedBrunFactor M = pBF_min.
            have h_pf_z_ge_min : pBF_min ≤ pairedBrunFactor z :=
              pairedBrunFactor_antitone hz_le_M
            -- AtSqrt at n.
            have hAtSqrt_n : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
                ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                  + refinedReservoir n (Nat.sqrt n) := hAtSqrtBd n hn
            -- Antitonicity.
            have h_anti : (goldbachSiftedPair n z : ℝ) ≤
                (goldbachSiftedPair n (Nat.sqrt n) : ℝ) :=
              goldbachSiftedPair_antitone_z_real n h_z_sqrt
            -- pairedBrunFactor (√n) ≤ 1.
            have h_pf_sqrt_le_one : pairedBrunFactor (Nat.sqrt n) ≤ 1 :=
              pairedBrunFactor_le_one _
            -- Reservoir at √n = at z.
            have h_res_eq : refinedReservoir n (Nat.sqrt n) = refinedReservoir n z := by
              simp [refinedReservoir_def]
            -- Main chain.
            have hCnn : 0 ≤ C := le_of_lt hCpos
            have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
            -- C · n · pairedBrunFactor (√n) ≤ C · n · 1 = C · n.
            have h_main_chain :
                C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) ≤ C * (n : ℝ) := by
              have : C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                  ≤ C * (n : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left h_pf_sqrt_le_one
                  (mul_nonneg hCnn h_n_nn)
              linarith [this]
            -- C · n = (C / pBF_min) · n · pBF_min ≤ C_bd · n · pairedBrunFactor z.
            have h_C_n_eq : C * (n : ℝ) = C_bd * (n : ℝ) * pBF_min := by
              rw [hC_bd_def]
              have hne : pBF_min ≠ 0 := ne_of_gt hpBF_min_pos
              field_simp
            have h_bridge : C * (n : ℝ) ≤ C_bd * (n : ℝ) * pairedBrunFactor z := by
              rw [h_C_n_eq]
              apply mul_le_mul_of_nonneg_left h_pf_z_ge_min
              exact mul_nonneg (le_of_lt hC_bd_pos) h_n_nn
            have h_main_bd : C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                ≤ C_bd * (n : ℝ) * pairedBrunFactor z :=
              le_trans h_main_chain h_bridge
            -- C_bd ≤ C₁.
            have h_C_bd_le_C₁ : C_bd ≤ C₁ := by
              rw [hC₁_def]
              have : C_bd ≤ max C_resid C_bd := le_max_right _ _
              linarith
            have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
            have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
              mul_nonneg h_n_nn h_pf_nn
            have h_C_to_C₁ : C_bd * (n : ℝ) * pairedBrunFactor z
                ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
              have : C_bd * ((n : ℝ) * pairedBrunFactor z)
                  ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
                mul_le_mul_of_nonneg_right h_C_bd_le_C₁ h_n_pf_nn
              linarith [this]
            calc (goldbachSiftedPair n z : ℝ)
                ≤ (goldbachSiftedPair n (Nat.sqrt n) : ℝ) := h_anti
              _ ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                  + refinedReservoir n (Nat.sqrt n) := hAtSqrt_n
              _ ≤ C_bd * (n : ℝ) * pairedBrunFactor z
                  + refinedReservoir n (Nat.sqrt n) := by linarith
              _ ≤ C₁ * (n : ℝ) * pairedBrunFactor z
                  + refinedReservoir n (Nat.sqrt n) := by linarith
              _ = C₁ * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z := by
                  rw [h_res_eq]
    · -- z < √n.  Use hResid via z < √n disjunct.
      have h := hResidBd n z hn (Or.inr h_z_lt_sqrt)
      have h_resid_le_C₁ : C_resid ≤ C₁ := by
        rw [hC₁_def]
        have : C_resid ≤ max C_resid C_bd := le_max_left _ _
        linarith
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
      have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
      have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
        mul_nonneg h_n_nn h_pf_nn
      have h_main_le : C_resid * (n : ℝ) * pairedBrunFactor z
          ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
        have : C_resid * ((n : ℝ) * pairedBrunFactor z)
            ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
          mul_le_mul_of_nonneg_right h_resid_le_C₁ h_n_pf_nn
        linarith [this]
      linarith

/-! ## Section 5 — The forward bridge

We prove the headline bridge:

```
AtSqrt + MertensLower + MertensUpperAtSqrt + ResidualLowRegion
  ⇒  Absorption .
```

Strategy: use `residual_enlarged_helper` to obtain an enlarged
residual with threshold `max(N₀_lower, N₀_upper, 3) + 1`.  Then split
on `n` vs the enlarged threshold and `z` vs `Nat.sqrt n`, using the
enlarged residual for low region and AtSqrt + Mertens for the high
region. -/

/-- **The forward bridge.**  The four residual sub-Props jointly
close `PairedMainTermAbsorption`.

The proof uses `residual_enlarged_helper` to absorb the
"intermediate-`n`" subregion (`N₀_resid ≤ n < N₀_combined`), so the
Mertens bounds only need to apply for `n ≥ N₀_combined`. -/
theorem absorption_of_atSqrt_and_residuals
    (hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrt)
    (hLower : PairedBrunFactorMertensLower)
    (hUpperSqrt : PairedBrunFactorMertensUpperAtSqrt)
    (hResid : PairedMainTermResidualLowRegion) :
    PairedMainTermAbsorption := by
  classical
  -- Unpack the Mertens hypotheses.
  obtain ⟨C, hCpos, hAtSqrtBd⟩ := hAtSqrt
  obtain ⟨K, N₀_lower, hKpos, hLowerBd⟩ := hLower
  obtain ⟨C', N₀_upper, hC'pos, hUpperBd⟩ := hUpperSqrt
  -- Enlarged residual threshold.
  set M : ℕ := max (max N₀_lower N₀_upper) 3 + 1 with hM_def
  -- Use `residual_enlarged_helper` to extend residual to threshold M.
  obtain ⟨C_resid', hC_resid'_pos, hResidBd'⟩ :=
    residual_enlarged_helper ⟨C, hCpos, hAtSqrtBd⟩ hResid M
  -- Bridge constant for Region II.
  set C_bridge : ℝ := C * C' / (K : ℝ) with hC_bridge_def
  have hKpos_real : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hC_bridge_nn : 0 ≤ C_bridge := by
    rw [hC_bridge_def]
    apply div_nonneg
    · exact mul_nonneg (le_of_lt hCpos) (le_of_lt hC'pos)
    · exact le_of_lt hKpos_real
  -- Uniform absorption constant.
  set C₁ : ℝ := max C_resid' C_bridge + 1 with hC₁_def
  have hC₁pos : 0 < C₁ := by
    rw [hC₁_def]
    have : 0 ≤ max C_resid' C_bridge :=
      le_max_of_le_left (le_of_lt hC_resid'_pos)
    linarith
  refine ⟨C₁, hC₁pos, ?_⟩
  intro n z hn
  -- Case: n < M OR z < √n.  Use enlarged residual.
  by_cases h_low : n < M ∨ z < Nat.sqrt n
  · have h := hResidBd' n z hn h_low
    have h_resid_le_C₁ : C_resid' ≤ C₁ := by
      rw [hC₁_def]
      have : C_resid' ≤ max C_resid' C_bridge := le_max_left _ _
      linarith
    have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
    have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
      mul_nonneg h_n_nn h_pf_nn
    have h_main_le : C_resid' * (n : ℝ) * pairedBrunFactor z
        ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
      have : C_resid' * ((n : ℝ) * pairedBrunFactor z)
          ≤ C₁ * ((n : ℝ) * pairedBrunFactor z) :=
        mul_le_mul_of_nonneg_right h_resid_le_C₁ h_n_pf_nn
      linarith [this]
    linarith
  · -- ¬ (n < M ∨ z < √n): so n ≥ M and z ≥ √n.
    push_neg at h_low
    obtain ⟨hn_ge_M, hz_ge_sqrt⟩ := h_low
    have hn_ge_3 : 3 ≤ n := by
      have h3 : 3 ≤ M := by
        rw [hM_def]
        have : 3 ≤ max (max N₀_lower N₀_upper) 3 := le_max_right _ _
        omega
      omega
    have hn_ge_lower : N₀_lower ≤ n := by
      have : N₀_lower ≤ M := by
        rw [hM_def]
        have : N₀_lower ≤ max (max N₀_lower N₀_upper) 3 :=
          le_max_of_le_left (le_max_left _ _)
        omega
      omega
    have hn_ge_upper : N₀_upper ≤ n := by
      have : N₀_upper ≤ M := by
        rw [hM_def]
        have : N₀_upper ≤ max (max N₀_lower N₀_upper) 3 :=
          le_max_of_le_left (le_max_right _ _)
        omega
      omega
    -- Split on z vs n - 1.
    by_cases h_z_collapse : n - 1 ≤ z
    · -- Sift collapse.
      have h_sift_zero : (goldbachSiftedPair n z : ℝ) = 0 :=
        goldbachSiftedPair_eq_zero_of_large_z_real hn_ge_3 h_z_collapse
      rw [h_sift_zero]
      have h_main_nn : 0 ≤ C₁ * (n : ℝ) * pairedBrunFactor z := by
        apply mul_nonneg
        · apply mul_nonneg (le_of_lt hC₁pos) (by exact_mod_cast Nat.zero_le _)
        · exact le_of_lt (pairedBrunFactor_pos z)
      have h_res_nn : 0 ≤ refinedReservoir n z := refinedReservoir_nonneg n z
      linarith
    · -- √n ≤ z < n - 1.  Use AtSqrt + Mertens.
      push_neg at h_z_collapse
      have hz_lt_n : z < n := by omega
      have hAtSqrt_n : (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + refinedReservoir n (Nat.sqrt n) := hAtSqrtBd n hn
      have h_anti : (goldbachSiftedPair n z : ℝ) ≤
          (goldbachSiftedPair n (Nat.sqrt n) : ℝ) :=
        goldbachSiftedPair_antitone_z_real n hz_ge_sqrt
      have h_upper : pairedBrunFactor (Nat.sqrt n) ≤
          C' / (Real.log (n : ℝ))^2 := hUpperBd n hn_ge_upper
      have h_lower : (K : ℝ) / (Real.log (n : ℝ))^2 ≤ pairedBrunFactor z :=
        hLowerBd n z hn_ge_lower hz_ge_sqrt hz_lt_n
      have h_res_eq : refinedReservoir n (Nat.sqrt n) = refinedReservoir n z := by
        simp [refinedReservoir_def]
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        apply Real.log_pos
        have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_3
        linarith
      have hlog_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
      have hC'nn : 0 ≤ C' := le_of_lt hC'pos
      have hCnn : 0 ≤ C := le_of_lt hCpos
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
      have h_main_chain :
          C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) ≤
            C * (n : ℝ) * (C' / (Real.log (n : ℝ))^2) := by
        apply mul_le_mul_of_nonneg_left h_upper
        exact mul_nonneg hCnn h_n_nn
      have h_bridge_le : C * (n : ℝ) * (C' / (Real.log (n : ℝ))^2) ≤
          C_bridge * (n : ℝ) * pairedBrunFactor z := by
        have h_lhs_eq : C * (n : ℝ) * (C' / (Real.log (n : ℝ))^2) =
            C_bridge * (n : ℝ) * ((K : ℝ) / (Real.log (n : ℝ))^2) := by
          rw [hC_bridge_def]
          have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos_real
          field_simp
        rw [h_lhs_eq]
        apply mul_le_mul_of_nonneg_left h_lower
        apply mul_nonneg hC_bridge_nn h_n_nn
      have h_main_bound : C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) ≤
          C_bridge * (n : ℝ) * pairedBrunFactor z :=
        le_trans h_main_chain h_bridge_le
      have hC_bridge_le_C₁ : C_bridge ≤ C₁ := by
        rw [hC₁_def]
        have : C_bridge ≤ max C_resid' C_bridge := le_max_right _ _
        linarith
      have h_pf_nn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
      have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
        mul_nonneg h_n_nn h_pf_nn
      have h_C_to_C₁ : C_bridge * (n : ℝ) * pairedBrunFactor z ≤
          C₁ * (n : ℝ) * pairedBrunFactor z := by
        have : C_bridge * ((n : ℝ) * pairedBrunFactor z) ≤
            C₁ * ((n : ℝ) * pairedBrunFactor z) :=
          mul_le_mul_of_nonneg_right hC_bridge_le_C₁ h_n_pf_nn
        linarith [this]
      calc (goldbachSiftedPair n z : ℝ)
          ≤ (goldbachSiftedPair n (Nat.sqrt n) : ℝ) := h_anti
        _ ≤ C * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + refinedReservoir n (Nat.sqrt n) := hAtSqrt_n
        _ ≤ C_bridge * (n : ℝ) * pairedBrunFactor z
            + refinedReservoir n (Nat.sqrt n) := by linarith
        _ ≤ C₁ * (n : ℝ) * pairedBrunFactor z + refinedReservoir n (Nat.sqrt n) := by
            linarith
        _ = C₁ * (n : ℝ) * pairedBrunFactor z + refinedReservoir n z := by
            rw [h_res_eq]

end PathCPairedBrunLargeZ
end Gdbh
