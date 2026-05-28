/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P9-T2 (Phase 9 / Path C — Brun main-term inequality:
  unsatisfiability catch + nontrivial-error refactor)
-/
import Gdbh.PathC_BrunSieve
import Gdbh.PathC_BrunClosure
import Gdbh.PathC_BrunCombDecay
import Gdbh.PathC_MertensProof
import Gdbh.PathC_Final

/-!
# Path C — Phase 9 / P9-T2: `BrunMainTerm pairedBrunFactor brunErrorWitness`

## Mission

The Phase 8 reduced bundle `PathC_Phase8ReducedContent` retains, among its
three open analytic fields, the Prop

```
brunMain : BrunMainTerm pairedBrunFactor brunErrorWitness
```

where `pairedBrunFactor z = ∏_{3 ≤ p ≤ z, p prime} (1 - 2/p)` is the
paired Brun main-term factor, and `brunErrorWitness ≡ 0` is the zero
error reservoir picked by P8-T3.  Unfolded:

```
IsBrunMainTermFactor pairedBrunFactor ∧
  ∃ C₁ > 0, ∀ N z, 0 < N → (siftedCount N z : ℝ) ≤ C₁ · N · pairedBrunFactor z .
```

The `IsBrunMainTermFactor` half is closed in `PathC_Final` (the lemma
`pairedBrunFactor_isFactor`).  The substantive half is the
**inclusion–exclusion sift inequality** with no additive error.

## P9-T2 finding (the catch)

The Prop is **asymptotically unsatisfiable**: for every positive
constant `C₁`, the inequality

```
1 = siftedCount 1 z  ≤  C₁ · 1 · pairedBrunFactor z
```

fails for `z` sufficiently large, because `pairedBrunFactor z → 0`
(this is the *paired-sieve Mertens decay*, recorded in
`PathC_MertensProof.PairedBrunMertensThirdGap`).  In quantitative form
the Brun paired-sieve main-term factor satisfies

```
pairedBrunFactor z  ≤  C / (log z)^2
```

(open in mathlib v4.29.1, but mathematically standard).  Combined with
`siftedCount 1 z = 1` (proved here, `siftedCount_one`), this rules out
the `B(N, z) = 0` shape: no fixed `C₁` can dominate `1` by a quantity
that tends to zero.

## Comparison with the analogous P7-T4 / P8-T3 pattern

The analogous `BrunMainTerm` closure at the Phase 7/8 level
(`Gdbh.PathCBrunClosure.brunMainTerm_trivial_witness`) uses the
worst-case error reservoir `B(N, z) = N`, which absorbs all the
analytic content into the *additive* term and proves the closure
trivially because `siftedCount N z ≤ N`.  P8-T3's refactor to
`B(N, z) = 0` was a bookkeeping simplification valid at the *interface*
level — it satisfies `BrunCombinatorialErrorDecay` trivially because
`0 ≤ N / (log N)^2` — but it shifts the entire analytic burden onto
the `BrunMainTerm` inequality, which (as documented here) becomes
*unsatisfiable* for the canonical paired Brun factor.

## P9-T2 deliverables

The interface is therefore restored by **reverting `B` to the worst-case
reservoir** `B(N, z) = N` at the Phase 9 closure layer.  The new
field
```
BrunMainTerm pairedBrunFactor (fun N _ => (N : ℝ))
```
is provable axiom-cleanly using the same `siftedCount ≤ N` trick as
P7-T4's `brunMainTerm_trivial_witness`.

This file produces:

* `siftedCount_one`: `siftedCount 1 z = 1` for every `z` (the catch
  witness: `{1}` is always sifted, since the integer `1` has no prime
  divisors).
* `pairedBrunFactor_le_one_third_of_three_le`: for `3 ≤ z`,
  `pairedBrunFactor z ≤ 1/3` (one fixed factor `(1-2/3) = 1/3` enters
  the product, and all other factors are in `(0, 1]`).  Quantitative
  *first-instance witness* that small `C₁` does not suffice.
* `pairedBrunMertensThirdGap_disproves_brunMain_pairedBrunFactor_zero`:
  the conditional impossibility theorem.  Assuming
  `PairedBrunMertensThirdGap` (the open paired-Brun Mertens gap),
  `BrunMainTerm pairedBrunFactor brunErrorWitness` is **false**.
* `brunMainTerm_pairedBrunFactor_worstCaseError`: the refactor,
  proving `BrunMainTerm pairedBrunFactor (fun N _ => (N : ℝ))`
  axiom-cleanly (no Mertens gap needed; pure `siftedCount ≤ N` argument).
* `pathC_p9_t2_summary`: a documentation `True` theorem recording the
  unsatisfiability catch and the proposed refactor.

All deliverables are axiom-clean: only `propext`, `Classical.choice`,
`Quot.sound` are used.
-/

namespace Gdbh
namespace PathCBrunMainProof

open Real Finset
open Gdbh.PathCBrunSieve
open Gdbh.PathCMertensProof

/-! ## Section 1 — The "catch" witness: `siftedCount 1 z = 1` -/

/-- The sifted set at `N = 1` is the singleton `{1}` for every choice of
sieving threshold `z`.  Indeed, `1` lies in `[1, 1]` and has no prime
divisor at all (primes never divide `1`), so it survives every sieve. -/
theorem siftedSet_one_eq (z : ℕ) : siftedSet 1 z = ({1} : Finset ℕ) := by
  apply Finset.ext
  intro n
  rw [mem_siftedSet, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hn1, hnN⟩, _⟩
    -- `1 ≤ n ≤ 1` forces `n = 1`.
    exact Nat.le_antisymm hnN hn1
  · rintro rfl
    refine ⟨⟨le_refl 1, le_refl 1⟩, ?_⟩
    intro p _ hpr hp_dvd
    -- A prime cannot divide `1`.
    exact (Nat.Prime.one_lt hpr).ne' (Nat.eq_one_of_dvd_one hp_dvd)

/-- **The catch witness.**  `siftedCount 1 z = 1` for every sieving
threshold `z`.  This is the constant lower-bound shape that the
`B(N, z) = 0` form of `BrunMainTerm` has to dominate. -/
theorem siftedCount_one (z : ℕ) : siftedCount 1 z = 1 := by
  unfold siftedCount
  rw [siftedSet_one_eq]
  simp

/-! ## Section 2 — `pairedBrunFactor z ≤ 1/3` for `z ≥ 3`

The product `pairedBrunFactor z` over primes in `[3, z]` always
contains the factor `(1 - 2/3) = 1/3` whenever `3 ≤ z`, and all
remaining factors are in `(0, 1]`.  Hence `pairedBrunFactor z ≤ 1/3`.
This is the simplest quantitative *catch witness* for the
unsatisfiability of `BrunMainTerm pairedBrunFactor brunErrorWitness`. -/

/-- For an odd prime `p ≥ 3`, the factor `1 - 2/p` is in `[0, 1]`. -/
private lemma one_sub_two_div_le_one {p : ℕ} (hp : 3 ≤ p) :
    (1 : ℝ) - 2 / (p : ℝ) ≤ 1 := by
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have h_two_div_nn : (0 : ℝ) ≤ 2 / (p : ℝ) :=
    div_nonneg (by norm_num) (le_of_lt hp_pos)
  linarith

private lemma one_sub_two_div_nonneg {p : ℕ} (hp : 3 ≤ p) :
    (0 : ℝ) ≤ 1 - 2 / (p : ℝ) :=
  le_of_lt (one_sub_two_div_prime_pos hp)

/-- **Quantitative catch witness.**  For `3 ≤ z`,
`pairedBrunFactor z ≤ 1/3`.

Proof: the filter `(Finset.Icc 3 z).filter Nat.Prime` contains `3`
(since `3` is prime and `3 ≤ 3 ≤ z`); singling out the factor
`(1 - 2/3) = 1/3` and bounding all remaining factors by `1` (each is
in `(0, 1]`) gives the claim. -/
theorem pairedBrunFactor_le_one_third_of_three_le {z : ℕ} (hz : 3 ≤ z) :
    pairedBrunFactor z ≤ 1 / 3 := by
  unfold pairedBrunFactor
  -- The singleton `{3}` is a subset of the filter, and the factor at
  -- `p = 3` equals `1 - 2/3 = 1/3`.
  have h3_prime : Nat.Prime 3 := by decide
  have h3_mem : (3 : ℕ) ∈ (Finset.Icc 3 z).filter Nat.Prime := by
    refine Finset.mem_filter.mpr ⟨?_, h3_prime⟩
    exact Finset.mem_Icc.mpr ⟨le_refl 3, hz⟩
  have hsub : ({3} : Finset ℕ) ⊆ (Finset.Icc 3 z).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    rw [hp]; exact h3_mem
  -- All factors `(1 - 2/p)` are in `[0, 1]` for `p ≥ 3`.
  have h_nn : ∀ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
      (0 : ℝ) ≤ 1 - 2 / (p : ℝ) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    exact one_sub_two_div_nonneg hp3
  have h_extra_le_one : ∀ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
      p ∉ ({3} : Finset ℕ) → (1 - 2 / (p : ℝ)) ≤ 1 := by
    intro p hp _
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    exact one_sub_two_div_le_one hp3
  -- Use `Finset.prod_le_prod_of_subset_of_le_one`: smaller filter →
  -- larger product (factors `≤ 1`).
  have hprod_le :
      ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 - 2 / (p : ℝ))
        ≤ ∏ p ∈ ({3} : Finset ℕ), (1 - 2 / (p : ℝ)) :=
    Finset.prod_le_prod_of_subset_of_le_one hsub h_nn h_extra_le_one
  -- Compute the right-hand side: a single factor `1 - 2/3 = 1/3`.
  have h_single :
      ∏ p ∈ ({3} : Finset ℕ), (1 - 2 / (p : ℝ)) = 1 / 3 := by
    simp [Finset.prod_singleton]; ring
  linarith [hprod_le, h_single.le, h_single.ge]

/-! ## Section 3 — Conditional disproof of
`BrunMainTerm pairedBrunFactor brunErrorWitness`

Assuming the named open Prop `PairedBrunMertensThirdGap` (the
paired-Brun Mertens upper bound `pairedBrunFactor z ≤ C / (log z)^2`),
we show that **for every** candidate constant `C₁ > 0`, taking `N = 1`
and `z` large enough forces a contradiction with the inequality

```
siftedCount 1 z = 1 ≤ C₁ · 1 · pairedBrunFactor z + 0 .
```

Because `pairedBrunFactor z` is bounded by `C / (log z)^2` which tends
to `0` as `z → ∞`, no finite `C₁` can keep the right-hand side `≥ 1`.

The argument is encoded as: a candidate `C₁` is supplied, the gap
delivers `pairedBrunFactor z ≤ C / (log z)^2`, and we choose `z`
explicitly large enough that `C₁ · C / (log z)^2 < 1`.  Concretely,
`z = Nat.ceil (Real.exp (Real.sqrt (C₁ · C + 1)))` works.

To avoid heavy mathlib work on `Nat.ceil`/`Real.exp`, we phrase the
disproof at the level of the `IsLUB`-free statement
`pairedBrunFactor_le_one_third_of_three_le` for `C₁ ≤ 3` — that already
covers the smallest interesting case — and rely on the open
`PairedBrunMertensThirdGap` for the general statement. -/

/-- **Conditional impossibility.**  Assuming the named open Prop
`PairedBrunMertensThirdGap`, the bundle field
`BrunMainTerm pairedBrunFactor brunErrorWitness` is unsatisfiable.

Proof sketch.  Suppose for contradiction we have `C₁ > 0` with the
inequality.  Specialise to `N = 1` (legal because `0 < 1`):
`siftedCount 1 z ≤ C₁ · pairedBrunFactor z`.  By `siftedCount_one`,
the left-hand side equals `1`.  By `PairedBrunMertensThirdGap`, there
exist `C, z₀` with `pairedBrunFactor z ≤ C / (log z)^2` for `z ≥ z₀`.
Choose `z` large enough that `(log z)^2 > C · C₁`; then
`C₁ · pairedBrunFactor z ≤ C₁ · C / (log z)^2 < 1`, contradicting
`1 ≤ C₁ · pairedBrunFactor z`.

The choice "`z` large enough" is supplied by `Real.tendsto_log_atTop`
applied at the natural number sequence, yielding `Real.log z`
unbounded; squaring preserves the divergence.  Mathlib furnishes this
via `Real.tendsto_log_atTop` and `Filter.Tendsto.comp`. -/
theorem pairedBrunMertensThirdGap_disproves_brunMain
    (hGap : PairedBrunMertensThirdGap) :
    ¬ Gdbh.PathCBrunSieve.BrunMainTerm pairedBrunFactor
        Gdbh.PathCBrunCombDecay.brunErrorWitness := by
  rintro ⟨_hFactor, C₁, hC₁pos, hBound⟩
  obtain ⟨C, z₀, hCpos, hGapBound⟩ := hGap
  -- Choose a real threshold `L` with `(log L)^2 > C * C₁`.
  -- Pick `L := Real.exp (Real.sqrt (C * C₁ + 1) + 1)`.
  -- Then `log L = √(C·C₁ + 1) + 1 ≥ √(C·C₁ + 1) > 0`, so
  -- `(log L)^2 ≥ C · C₁ + 1 > C · C₁`.
  -- Then any `z ≥ max(z₀, ⌈L⌉)` satisfies the contradiction.
  set s : ℝ := Real.sqrt (C * C₁ + 1) + 1 with hs_def
  have hCC₁_nonneg : 0 ≤ C * C₁ := le_of_lt (mul_pos hCpos hC₁pos)
  have hCC₁₁_pos : 0 < C * C₁ + 1 := by linarith
  have hsqrt_nn : 0 ≤ Real.sqrt (C * C₁ + 1) := Real.sqrt_nonneg _
  have hs_pos : 0 < s := by
    have : (0 : ℝ) < 1 := by norm_num
    linarith
  set L : ℝ := Real.exp s with hL_def
  have hL_pos : 0 < L := Real.exp_pos s
  have hL_gt_one : 1 < L := by
    rw [hL_def]
    have : Real.exp 0 < Real.exp s := Real.exp_lt_exp.mpr hs_pos
    simpa using this
  -- Choose `z := max (Nat.ceil L) z₀ + 1`, ensuring `z₀ ≤ z` and `(z:ℝ) > L`.
  set z : ℕ := max (Nat.ceil L) z₀ + 1 with hz_def
  have hz_ge_z₀ : z₀ ≤ z := by
    have : z₀ ≤ max (Nat.ceil L) z₀ := le_max_right _ _
    omega
  have hz_ge_ceilL : Nat.ceil L ≤ z := by
    have : Nat.ceil L ≤ max (Nat.ceil L) z₀ := le_max_left _ _
    omega
  have hz_real_gt_L : L < (z : ℝ) := by
    -- `L ≤ Nat.ceil L ≤ z - 1 < z`.
    have h1 : L ≤ (Nat.ceil L : ℝ) := Nat.le_ceil L
    have h2 : (Nat.ceil L : ℝ) ≤ ((z - 1 : ℕ) : ℝ) := by
      have : Nat.ceil L ≤ z - 1 := by
        have hz1 : Nat.ceil L + 1 ≤ z := by
          calc Nat.ceil L + 1
              ≤ max (Nat.ceil L) z₀ + 1 := by
                exact Nat.add_le_add_right (le_max_left _ _) 1
            _ = z := by rw [hz_def]
        omega
      exact_mod_cast this
    have h3 : ((z - 1 : ℕ) : ℝ) < (z : ℝ) := by
      have hz_pos : 1 ≤ z := by
        rw [hz_def]; exact Nat.succ_le_succ (Nat.zero_le _)
      have hcast : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
        rw [Nat.cast_sub hz_pos]; push_cast; ring
      rw [hcast]; linarith
    linarith
  have hz_pos_real : (0 : ℝ) < (z : ℝ) := by linarith
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  -- From `L < z` deduce `s = log L < log z`.
  have hs_lt_logz : s < Real.log (z : ℝ) := by
    have hLogLt : Real.log L < Real.log (z : ℝ) :=
      Real.log_lt_log hL_pos hz_real_gt_L
    rwa [hL_def, Real.log_exp] at hLogLt
  have hsqrt_lt_logz :
      Real.sqrt (C * C₁ + 1) < Real.log (z : ℝ) := by
    have h_lt_s : Real.sqrt (C * C₁ + 1) < s := by
      rw [hs_def]; linarith
    linarith
  -- Hence `(log z)^2 > C·C₁ + 1`.
  have hlogz_sq_gt : C * C₁ + 1 < (Real.log (z : ℝ))^2 := by
    have h_sqrt_sq : Real.sqrt (C * C₁ + 1) ^ 2 = C * C₁ + 1 :=
      Real.sq_sqrt (le_of_lt hCC₁₁_pos)
    have h_sqrt_nn : 0 ≤ Real.sqrt (C * C₁ + 1) := Real.sqrt_nonneg _
    have hlogz_nn : 0 ≤ Real.log (z : ℝ) := le_of_lt hlogz_pos
    have := sq_lt_sq' (by linarith : -Real.log (z : ℝ) < Real.sqrt (C * C₁ + 1))
                        hsqrt_lt_logz
    -- `this : (Real.sqrt (C * C₁ + 1))^2 < (Real.log z)^2`.
    rw [h_sqrt_sq] at this
    linarith
  -- Apply the Brun main inequality at N=1, z:
  have hN_pos : 0 < (1 : ℕ) := by norm_num
  have hMain₀ :=  hBound 1 z hN_pos
  have hMain :
      (siftedCount 1 z : ℝ)
        ≤ C₁ * (1 : ℝ) * pairedBrunFactor z
          + Gdbh.PathCBrunCombDecay.brunErrorWitness 1 z := by
    have hc : ((1 : ℕ) : ℝ) = (1 : ℝ) := by norm_cast
    rw [hc] at hMain₀
    exact hMain₀
  have hSC_one : (siftedCount 1 z : ℝ) = 1 := by
    have := siftedCount_one z
    exact_mod_cast this
  have h_err_zero :
      Gdbh.PathCBrunCombDecay.brunErrorWitness 1 z = 0 := by
    simp [Gdbh.PathCBrunCombDecay.brunErrorWitness_def]
  rw [hSC_one, h_err_zero] at hMain
  -- `1 ≤ C₁ · 1 · pairedBrunFactor z + 0`
  have hMainSimp : (1 : ℝ) ≤ C₁ * pairedBrunFactor z := by linarith
  -- Now bound the right-hand side via the Mertens gap.
  have hMertensZ : pairedBrunFactor z ≤ C / (Real.log (z : ℝ))^2 :=
    hGapBound z hz_ge_z₀
  have hpBF_nn : (0 : ℝ) ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
  -- `C₁ * pairedBrunFactor z ≤ C₁ * (C / (log z)^2) = (C₁ * C) / (log z)^2`.
  have hRHS_le : C₁ * pairedBrunFactor z ≤ C₁ * C / (Real.log (z : ℝ))^2 := by
    have h1 : C₁ * pairedBrunFactor z ≤ C₁ * (C / (Real.log (z : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hMertensZ (le_of_lt hC₁pos)
    have h2 : C₁ * (C / (Real.log (z : ℝ))^2) = C₁ * C / (Real.log (z : ℝ))^2 := by
      ring
    linarith
  -- And `(C₁ * C) / (log z)^2 < 1` because `(log z)^2 > C * C₁ + 1 > C₁ * C`.
  have hlogz_sq_pos : 0 < (Real.log (z : ℝ))^2 := by positivity
  have hCC₁_eq : C * C₁ = C₁ * C := by ring
  have hlogz_sq_gt_C₁C : C₁ * C < (Real.log (z : ℝ))^2 := by
    rw [← hCC₁_eq]; linarith
  have hRHS_lt_one : C₁ * C / (Real.log (z : ℝ))^2 < 1 := by
    rw [div_lt_one hlogz_sq_pos]
    exact hlogz_sq_gt_C₁C
  -- Contradiction: `1 ≤ C₁ · pairedBrunFactor z ≤ (C₁ * C)/(log z)^2 < 1`.
  linarith [hMainSimp, hRHS_le, hRHS_lt_one]

/-! ## Section 4 — Refactor: nontrivial-error main-term witness

We now produce the **refactored** main-term witness, mirroring P7-T4's
`brunMainTerm_trivial_witness` but with the *paired* main-term factor
`pairedBrunFactor` in place of `brunMainTermWitnessFactor`.  This is
the natural restoration of the analytic interface after the P9-T2 catch
above: putting the error reservoir back to `B(N, z) = N` makes the
Brun main-term inequality trivially provable, while still giving the
downstream assembly enough room because `BrunErrorTerm` is satisfied
by `B(N, z) = N` only conditional on `N ≤ C₂ · N / (log N)^2`,
which fails — so the refactor must also adjust `BrunErrorTerm`'s
witness.

For now we provide the **closed** statement
`BrunMainTerm pairedBrunFactor (fun N _ => (N : ℝ))`, axiom-clean.
The companion `BrunErrorTerm` refactor lives at the bundle level
(future-work item recorded in `pathC_p9_t2_summary`). -/

/-- `pairedBrunFactor` is a Brun main-term factor (positive and
antitone).  This is the public version of the `private` lemma in
`PathC_Final`. -/
theorem pairedBrunFactor_isBrunMainTermFactor :
    Gdbh.PathCBrunSieve.IsBrunMainTermFactor pairedBrunFactor := by
  refine ⟨pairedBrunFactor_pos, ?_⟩
  intro a b hab
  unfold pairedBrunFactor
  have hsub : (Finset.Icc 3 a).filter Nat.Prime ⊆ (Finset.Icc 3 b).filter Nat.Prime := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, hpr⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, hpa⟩
    refine Finset.mem_filter.mpr ⟨?_, hpr⟩
    exact Finset.mem_Icc.mpr ⟨hp3, hpa.trans hab⟩
  refine Finset.prod_le_prod_of_subset_of_le_one hsub ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    exact one_sub_two_div_nonneg hp3
  · intro p hpb _hpa
    rcases Finset.mem_filter.mp hpb with ⟨hp_Icc, _⟩
    rcases Finset.mem_Icc.mp hp_Icc with ⟨hp3, _⟩
    exact one_sub_two_div_le_one hp3

/-- **P9-T2 refactor.**  With `M := pairedBrunFactor` and the *worst-case*
error reservoir `B(N, z) := N`, the Brun main-term inequality

```
siftedCount N z  ≤  C₁ · N · pairedBrunFactor z  +  N
```

holds with `C₁ = 1`.  This is the natural restoration of the
P7-T4-style trivial witness pattern to the paired Brun factor.

Proof: `siftedCount N z ≤ N` (trivial monotonicity) and
`C₁ · N · pairedBrunFactor z ≥ 0`, so the inequality holds
regardless. -/
theorem brunMainTerm_pairedBrunFactor_worstCaseError :
    Gdbh.PathCBrunSieve.BrunMainTerm pairedBrunFactor (fun N _ => (N : ℝ)) := by
  refine ⟨pairedBrunFactor_isBrunMainTermFactor, 1, by norm_num, ?_⟩
  intro N z _hN
  have hSift : (siftedCount N z : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast siftedCount_le N z
  have hMnn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_extra : 0 ≤ 1 * (N : ℝ) * pairedBrunFactor z :=
    mul_nonneg (by linarith) hMnn
  linarith

/-- Pure existential closure: a witness `(M, B)` with the *paired*
main-term factor exists. -/
theorem exists_brunMainTerm_pairedBrunFactor_witness :
    ∃ B : ℕ → ℕ → ℝ,
      Gdbh.PathCBrunSieve.BrunMainTerm pairedBrunFactor B :=
  ⟨fun N _ => (N : ℝ), brunMainTerm_pairedBrunFactor_worstCaseError⟩

/-! ## Section 5 — P9-T2 summary -/

/-- **P9-T2 summary, in proof form.**

**Finding.**  The Phase 8 reduced bundle field
`brunMain : BrunMainTerm pairedBrunFactor brunErrorWitness`
(with `brunErrorWitness ≡ 0`) is **asymptotically unsatisfiable**.
Quantitatively, `siftedCount 1 z = 1` for every `z` (proved here as
`siftedCount_one`), and `pairedBrunFactor z → 0` as `z → ∞`
(quantitatively, `pairedBrunFactor z ≤ C / (log z)^2`, the open Prop
`PairedBrunMertensThirdGap`).  Hence no constant `C₁ > 0` can satisfy
`1 ≤ C₁ · pairedBrunFactor z` for arbitrarily large `z`.  The conditional
disproof is `pairedBrunMertensThirdGap_disproves_brunMain`.

**Refactor.**  The interface is restored by replacing the zero error
reservoir with the worst-case reservoir `B(N, z) := N`.  The
refactored field `BrunMainTerm pairedBrunFactor (fun N _ => (N : ℝ))`
is closed axiom-cleanly here as
`brunMainTerm_pairedBrunFactor_worstCaseError`.

**Downstream impact.**  The Phase 8 bundle's
`PathC_Phase8ReducedContent.brunMain` field should be retyped from
`BrunMainTerm pairedBrunFactor brunErrorWitness` to
`BrunMainTerm pairedBrunFactor (fun N _ => (N : ℝ))`, with the
companion `BrunErrorTerm` field switched from `brunErrorWitness` to a
non-zero witness (the natural candidate is the same `B(N, z) := N`,
whose `BrunErrorTerm` closure requires the *honest* Brun combinatorial
estimate, not the trivial-witness pattern of P8-T3).  Equivalently,
both the main-term and error-term sides should run on a **nonzero**
error reservoir whose precise shape is dictated by Brun's combinatorial
truncation.

This refactor is *layer-2* (bundle restructuring) and not appropriate
to apply at the P9-T2 file-creation level; we record it here as a
named documentation theorem. -/
theorem pathC_p9_t2_summary : True := trivial

end PathCBrunMainProof
end Gdbh
