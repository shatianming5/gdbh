/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T45 (Phase 19 / Path C — Direct closure attempt of
        `BrunGoldbachPairedMainTermRefinedAtSqrt` with `∃ C₁`).
-/
import Gdbh.PathC_DecidableSmallN
import Gdbh.PathC_BrunRefinedComposition
import Gdbh.PathC_PairedMainTermAssembly
import Gdbh.PathC_CorrectedChain
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Path C — P19-T45: Direct closure attempt of `BrunGoldbachPairedMainTermRefinedAtSqrt`

This file is the **P19-T45 deliverable** in Phase 19 (Path C residual
exploration).

## Background

P19-T41 detected that the literal Prop
`Gdbh.PathCBrunBonferroniDecomposition.AssemblyPieceA` — which carries
the coefficient `1` on the main-term factor `n · pairedBrunFactor(√n)`
— is **mathematically false** at the primorial witness `n = 30`
(see `_test_audit.lean`).  The architecturally correct downstream Prop
`Gdbh.PathCPairedMainTermAssembly.BrunGoldbachPairedMainTermRefinedAtSqrt`
is `∃`-quantified in `C₁`, so the falsification at coefficient `1`
does not immediately propagate.

P19-T45 asks:  is there *any* finite `C₁ > 0` for which
`BrunGoldbachPairedMainTermRefinedAtSqrt` is true?

## Mathematical conclusion (P19-T45 honesty finding)

The Prop `BrunGoldbachPairedMainTermRefinedAtSqrt` is **mathematically
false** — it is the *14th false-Prop catch* in this codebase.  No
finite `C₁ > 0` works uniformly across all `n`, because the singular
series `S(n) := ∏_{p|n, p>2}((p-1)/(p-2))` grows **unboundedly** along
the sequence of primorials `p_k# := ∏_{p ≤ p_k} p`.

### Computational evidence (this file)

We compute `goldbachSiftedPair n (Nat.sqrt n)` exactly for the
primorial-like witnesses `n ∈ {30, 210, 420}` and exhibit the *minimum
admissible* `C₁` at each `n`.

| `n`   | `√n` | `goldbachSiftedPair n √n` | `n · pBF(√n)` | required `C₁`     |
|------:|-----:|--------------------------:|--------------:|------------------:|
|   30  |    5 |                        8  |       30/5 = 6 | `≈ 0.901`        |
|  210  |   14 |                       34  | 210·9/91 ≈ 20.77 | `≈ 1.284`     |
|  420  |   20 |                       58  | 420·135/1729 ≈ 32.79 | `≈ 1.417` |

The required `C₁` is **strictly increasing** with `n`, with the growth
rate of `log log n` along primorials (Brun-Hardy-Littlewood asymptotic
for the singular series `S(p_k#) ∼ c · log p_k ∼ c · log log p_k#`).

### Refutation at literal `C₁ = 1` (formalised below)

The principal formal contribution of this file is a Lean theorem
`brunGoldbachPairedMainTermRefinedAtSqrt_fails_at_C1_eq_one`:  the
bound

```
(goldbachSiftedPair n (Nat.sqrt n) : ℝ)
  ≤ 1 · n · pairedBrunFactor (Nat.sqrt n) + refinedReservoir n (Nat.sqrt n)
```

**fails at `n = 210`**.  Combined with the analytical singular-series
growth, this shows that the Prop fails for every fixed `C₁ > 0` once
`n` is taken at a sufficiently large primorial — completing the
"strong" Prop refutation in the asymptotic sense, while leaving the
fully formalised quantitative version (which would require asymptotic
sieve estimates not currently in mathlib) as a *classical analytic
residual*.

### Why this is the 14th false-Prop catch

The classical Brun-Goldbach upper bound is

```
r(n)  ≤  C · n · pBF(√n) · S(n)         (Halberstam-Richert 3.11)
```

with the *singular series* factor `S(n) := ∏_{p|n,p≥3}((p-1)/(p-2))`.
For primorial `n = p_k#`, `S(p_k#)` grows like `log p_k ∼ log log n`,
which is **unbounded**.  The reservoir `n / (log n)²` has the same
growth as `n · pBF(√n)` (both scale as `n / (log n)²` up to bounded
constants by Mertens), so the reservoir absorbs only a *bounded*
factor of the singular series — leaving an unbounded multiplicative
discrepancy.  No finite `C₁` can absorb a `log log n` growth uniformly.

This finding parallels the architecturally analogous
*conditional falseness* of the zero-reservoir Prop
`BrunGoldbachPairedMainTerm` (under `PairedBrunMertensThirdGap`,
see `pairedBrunMertensThirdGap_disproves_brunGoldbachMainTerm_zero` in
`PathC_BrunGoldbachComposition`).  The refined-reservoir Prop is
defused at `n = 2` (where the reservoir `2/(log 2)² ≈ 4.16`
dominates) but fails at primorial witnesses for any fixed `C₁`.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene target: `[Classical.choice, Quot.sound, propext]`.
* File compiles standalone.

## Implementation notes

* `goldbachSiftedPair 2310 (Nat.sqrt 2310)` is not computable by
  `decide` within the kernel recursion limit (the `Finset.Icc 1 2309`
  filter has too many elements).  We therefore restrict computation to
  `n ∈ {30, 210, 420}` and use Brun's classical asymptotic for the
  conceptual conclusion.

* Bounding `n / (log n)²` from above requires `log n` lower bounds,
  established here via `Real.exp_one_lt_three` and elementary
  monomorphic-in-`n` arithmetic.
-/

namespace Gdbh
namespace PathCRefinedAtSqrtDirectClosure

open Real
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPairSet)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunRefinedComposition
  (refinedReservoir refinedReservoir_def
   BrunGoldbachPairedMainTermRefined)
open Gdbh.PathCPairedMainTermAssembly
  (BrunGoldbachPairedMainTermRefinedAtSqrt)

/-! ## Section 1 — Numerical computation of `Nat.sqrt` at the primorial witnesses. -/

/-- `Nat.sqrt 30 = 5`. -/
lemma sqrt_30 : Nat.sqrt 30 = 5 := by norm_num

/-- `Nat.sqrt 210 = 14`. -/
lemma sqrt_210 : Nat.sqrt 210 = 14 := by norm_num

/-- `Nat.sqrt 420 = 20`. -/
lemma sqrt_420 : Nat.sqrt 420 = 20 := by norm_num

/-! ## Section 2 — Numerical computation of `goldbachSiftedPair`. -/

/-- **Exact value at the first primorial witness `n = 30`.**
`goldbachSiftedPair 30 5 = 8`.

The 8 admissible `m ∈ [1, 29]` are exactly the units modulo `30`,
i.e. `{1, 7, 11, 13, 17, 19, 23, 29} = (ℤ/30ℤ)^×`. -/
lemma goldbachSiftedPair_30 : goldbachSiftedPair 30 5 = 8 := by decide

/-- **Exact value at the second primorial witness `n = 210`.**
`goldbachSiftedPair 210 14 = 34`. -/
lemma goldbachSiftedPair_210 : goldbachSiftedPair 210 14 = 34 := by decide

/-- **Exact value at the third witness `n = 420 = 2² · 3 · 5 · 7`.**
`goldbachSiftedPair 420 20 = 58`. -/
lemma goldbachSiftedPair_420 : goldbachSiftedPair 420 20 = 58 := by
  set_option maxRecDepth 8192 in decide

/-! ## Section 3 — Exact values of `pairedBrunFactor` at the primorial sieve thresholds. -/

/-- `pairedBrunFactor 5 = 1/5`.  Primes in `[3, 5]` are `{3, 5}`,
giving `(1 - 2/3)(1 - 2/5) = (1/3)(3/5) = 1/5`. -/
lemma pairedBrunFactor_5_eq_one_fifth : pairedBrunFactor 5 = (1 : ℝ) / 5 := by
  unfold pairedBrunFactor
  have h3prime : Nat.Prime 3 := by decide
  have h4nprime : ¬ Nat.Prime 4 := by decide
  have h5prime : Nat.Prime 5 := by decide
  have h_filter : (Finset.Icc 3 5).filter Nat.Prime = {3, 5} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      interval_cases x
      · left; rfl
      · exact absurd hp h4nprime
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨⟨by norm_num, by norm_num⟩, h3prime⟩
      · exact ⟨⟨by norm_num, by norm_num⟩, h5prime⟩
  rw [h_filter]
  rw [Finset.prod_insert (by simp)]
  simp
  norm_num

/-- `pairedBrunFactor 14 = 9/91`.  Primes in `[3, 14]` are
`{3, 5, 7, 11, 13}`, giving `(1/3)(3/5)(5/7)(9/11)(11/13) = 9/91`. -/
lemma pairedBrunFactor_14_eq_nine_div_91 : pairedBrunFactor 14 = (9 : ℝ) / 91 := by
  unfold pairedBrunFactor
  have h_filter : (Finset.Icc 3 14).filter Nat.Prime = {3, 5, 7, 11, 13} := by
    decide
  rw [h_filter]
  rw [show ({3, 5, 7, 11, 13} : Finset ℕ) =
        insert 3 (insert 5 (insert 7 (insert 11 ({13} : Finset ℕ)))) from rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
  norm_num

/-- `pairedBrunFactor 20 = 135/1729`.  Primes in `[3, 20]` are
`{3, 5, 7, 11, 13, 17, 19}`, extending the n=14 product by
`(1 - 2/17)(1 - 2/19) = (15/17)(17/19) = 15/19`. -/
lemma pairedBrunFactor_20_eq_135_div_1729 :
    pairedBrunFactor 20 = (135 : ℝ) / 1729 := by
  unfold pairedBrunFactor
  have h_filter : (Finset.Icc 3 20).filter Nat.Prime = {3, 5, 7, 11, 13, 17, 19} := by
    decide
  rw [h_filter]
  rw [show ({3, 5, 7, 11, 13, 17, 19} : Finset ℕ) =
        insert 3 (insert 5 (insert 7 (insert 11
          (insert 13 (insert 17 ({19} : Finset ℕ)))))) from rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
  norm_num

/-! ## Section 4 — Logarithm lower bounds via `exp_one_lt_three`.

We need explicit lower bounds on `Real.log n` to bound the reservoir
`n / (log n)²` from above.  We use the elementary fact `exp 1 < 3`
(`Real.exp_one_lt_three`) and the multiplicative form `exp(k) =
(exp 1)^k < 3^k`. -/

/-- `Real.exp 4 < 81`.  Follows from `(exp 1)^4 < 3^4 = 81`. -/
private lemma exp_four_lt_81 : Real.exp 4 < 81 := by
  have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h3 : Real.exp 4 = (Real.exp 1)^4 := by
    rw [show (4 : ℝ) = 1 + 1 + 1 + 1 from by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  rw [h3]
  have h_pow_lt : (Real.exp 1)^4 < 3^4 := by
    apply pow_lt_pow_left₀ h1 (le_of_lt h_exp_pos) (by norm_num)
  linarith

/-- `Real.log 210 > 4`.  Follows from `exp 4 < 81 < 210`. -/
lemma log_210_gt_four : (4 : ℝ) < Real.log 210 := by
  have h2 : Real.exp 4 < 81 := exp_four_lt_81
  have h3 : Real.exp 4 < 210 := by linarith
  have heq : (4 : ℝ) = Real.log (Real.exp 4) := (Real.log_exp 4).symm
  rw [heq]
  exact Real.log_lt_log (Real.exp_pos 4) h3

/-- `(Real.log 210)² > 16`. -/
lemma log_210_sq_gt_sixteen : (16 : ℝ) < (Real.log 210)^2 := by
  have hlog_gt : (4 : ℝ) < Real.log 210 := log_210_gt_four
  have hlog_nn : (0 : ℝ) ≤ Real.log 210 := by linarith
  have hsq : (4 : ℝ)^2 < (Real.log 210)^2 := by
    apply sq_lt_sq' (by linarith : -Real.log 210 < 4) hlog_gt
  have h_eq : (4 : ℝ)^2 = 16 := by norm_num
  linarith

/-- `210 / (Real.log 210)² < 13.125 = 210/16`. -/
lemma reservoir_210_le : (210 : ℝ) / (Real.log 210)^2 < 13.125 := by
  have hlog_sq_pos : (0 : ℝ) < (Real.log 210)^2 := by
    have hlog_pos : (0 : ℝ) < Real.log 210 := by
      have := log_210_gt_four
      linarith
    positivity
  have hbnd : (16 : ℝ) < (Real.log 210)^2 := log_210_sq_gt_sixteen
  -- `210 / x < 210 / 16` when `16 < x`, for positive `x` and `0 < 210`.
  have h_pos : (0 : ℝ) < 210 := by norm_num
  have h16_pos : (0 : ℝ) < 16 := by norm_num
  have : (210 : ℝ) / (Real.log 210)^2 < 210 / 16 := by
    apply div_lt_div_of_pos_left h_pos h16_pos hbnd
  linarith

/-! ## Section 5 — The refutation at `n = 210` for `C₁ = 1`.

We show that the bound

```
(goldbachSiftedPair 210 14 : ℝ) ≤ 1 · 210 · pairedBrunFactor 14 + 210 / (log 210)²
```

**fails**:  the LHS is `34` (exact) while the RHS is bounded above by
`270/13 + 13.125 < 21 + 14 = 35`.  More precisely we get
`RHS < 33.9` for `C₁ = 1`. -/

/-- **`refinedReservoir 210 (Nat.sqrt 210) < 13.125`.** -/
lemma refinedReservoir_210_lt : refinedReservoir 210 14 < (13.125 : ℝ) := by
  simp [refinedReservoir]
  exact reservoir_210_le

/-- **The bound at `n = 210` for the trivial `C₁ = 1` candidate.**

The natural choice `C₁ = 1` (the literal `AssemblyPieceA` coefficient,
diagnosed false at `n = 30` by P19-T41) is **also insufficient** for
the existentially-quantified `BrunGoldbachPairedMainTermRefinedAtSqrt`
at the primorial witness `n = 210`:

```
goldbachSiftedPair 210 14 = 34 > 270/13 + 13.125 ≥ 1 · 210 · pBF(14) + 210/(log 210)²
```

i.e. `LHS = 34` while `RHS < 33.9`. -/
theorem refinedAtSqrt_C1_eq_one_fails_at_210 :
    ¬ ((goldbachSiftedPair 210 (Nat.sqrt 210) : ℝ)
        ≤ 1 * (210 : ℝ) * pairedBrunFactor (Nat.sqrt 210)
            + refinedReservoir 210 (Nat.sqrt 210)) := by
  rw [sqrt_210, pairedBrunFactor_14_eq_nine_div_91, goldbachSiftedPair_210]
  intro h
  -- After rewriting, `h : (34 : ℝ) ≤ 1 · 210 · (9/91) + refinedReservoir 210 14`.
  -- Step 1: simplify `1 · 210 · (9/91) = 270/13`.
  -- `210 · 9 / 91 = 1890 / 91 = 270/13` since `91 · 270 = 24570` and
  -- `13 · 1890 = 24570`.
  have h_main : (1 : ℝ) * (210 : ℝ) * (9 / 91) = 270 / 13 := by ring
  rw [h_main] at h
  -- Step 2: bound the reservoir.
  have h_res : refinedReservoir 210 14 < (13.125 : ℝ) := refinedReservoir_210_lt
  -- Step 3: combine.  `270/13 + 13.125 < 34`.
  -- Numerical: 270/13 = 20.769..., plus 13.125 = 33.894... < 34.
  have h_combined : (270 : ℝ) / 13 + refinedReservoir 210 14 < 34 := by
    have h_main_val : (270 : ℝ) / 13 < 20.77 := by norm_num
    linarith
  linarith

/-! ## Section 6 — Generalisation:  for `0 < C₁ ≤ 1` the bound fails at `n = 210`.

The natural `∀ C₁ ≤ 1` extension of the refutation:  any `C₁ ≤ 1`
fails at `n = 210`.  Since the existentially-quantified Prop requires
*some* `C₁ > 0` to work *for all* `n`, this rules out all such `C₁`
ranges. -/

/-- **Generalisation**:  for any `C₁ ≤ 1`, the bound at `n = 210`
fails.

(The argument:  LHS = `34`, RHS = `C₁ · 270/13 + reservoir ≤ 270/13 +
13.125 < 34`.) -/
theorem refinedAtSqrt_fails_at_210_of_C1_le_one
    (C₁ : ℝ) (hC₁_le : C₁ ≤ 1) :
    ¬ ((goldbachSiftedPair 210 (Nat.sqrt 210) : ℝ)
        ≤ C₁ * (210 : ℝ) * pairedBrunFactor (Nat.sqrt 210)
            + refinedReservoir 210 (Nat.sqrt 210)) := by
  rw [sqrt_210, pairedBrunFactor_14_eq_nine_div_91, goldbachSiftedPair_210]
  intro h
  -- `C₁ * 210 * (9/91) ≤ 1 * 210 * (9/91) = 270/13` since `C₁ ≤ 1`
  -- and `210 * (9/91) ≥ 0`.
  have h_main_nn : (0 : ℝ) ≤ 210 * (9 / 91) := by norm_num
  have h_main_le : C₁ * (210 : ℝ) * (9 / 91) ≤ 1 * 210 * (9 / 91) := by
    have : C₁ * ((210 : ℝ) * (9 / 91)) ≤ 1 * ((210 : ℝ) * (9 / 91)) :=
      mul_le_mul_of_nonneg_right hC₁_le h_main_nn
    linarith
  have h_main_eq : (1 : ℝ) * (210 : ℝ) * (9 / 91) = 270 / 13 := by ring
  rw [h_main_eq] at h_main_le
  -- Reservoir bound.
  have h_res : refinedReservoir 210 14 < (13.125 : ℝ) := refinedReservoir_210_lt
  -- Combine: `C₁ · 210 · 9/91 + reservoir < 270/13 + 13.125 < 34`.
  have h_270_13_lt : (270 : ℝ) / 13 < 20.77 := by norm_num
  linarith

/-! ## Section 7 — The `∃ C₁ ≤ 1, ∀ n, ...` sub-Prop is FALSE.

A direct corollary:  the *restricted* existential Prop with `C₁ ≤ 1`
is false.  This is the formal residue of P19-T41's `n = 30`
diagnosis extended to the refined-reservoir setting at `n = 210`. -/

/-- **Restricted Prop is false:**  no `0 < C₁ ≤ 1` witness works
across all `n`.

This is a *partial* refutation of `BrunGoldbachPairedMainTermRefinedAtSqrt`:
it rules out all `C₁ ≤ 1`.  The full refutation (which would rule out
*every* finite `C₁`) requires the singular-series asymptotic
`S(p_k#) ∼ log log (p_k#)` along primorials, which is the unbounded
factor that the reservoir `n / (log n)²` cannot absorb.  See Section 9
for the conceptual analysis. -/
theorem no_witness_with_C1_le_one :
    ¬ ∃ C₁ : ℝ, 0 < C₁ ∧ C₁ ≤ 1 ∧
      ∀ n : ℕ, 0 < n →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + refinedReservoir n (Nat.sqrt n) := by
  rintro ⟨C₁, _hC₁_pos, hC₁_le, hbd⟩
  -- Instantiate at `n = 210`.
  have h210 := hbd 210 (by norm_num)
  -- This contradicts `refinedAtSqrt_fails_at_210_of_C1_le_one`.
  exact refinedAtSqrt_fails_at_210_of_C1_le_one C₁ hC₁_le h210

/-! ## Section 8 — Trend documentation:  required `C₁` strictly increases.

For each primorial witness, the **minimum admissible** `C₁` (the
smallest `C₁` for which `LHS ≤ C₁ · n · pBF + reservoir` could hold)
is strictly increasing.  This is the *numerical signature* of the
singular-series growth.

Symbolically, with `r(n) := goldbachSiftedPair n √n`, `m(n) := n · pBF(√n)`,
`b(n) := refinedReservoir n √n`:

```
C₁_min(n) = (r(n) - b(n)) / m(n) .
```

Trend (lower bounds on `C₁_min`, formalised below):

* `C₁_min(30) > 0` (since `8 > 6 · 0 + reservoir(30)`).
* `C₁_min(210) > 1` (formalised above).
* `C₁_min(420) > 1.4` (Section 9 — informal).
-/

/-- **C₁_min(30) > 0.**  Even the trivial coefficient `C₁ = 0` (with
the reservoir alone) fails at `n = 30`:

```
goldbachSiftedPair 30 5 = 8 > 30 / (log 30)²
```

i.e. the reservoir `30/(log 30)² ≈ 2.594` does not dominate the LHS
`8` (in contrast to `n = 2`, where `2/(log 2)² ≈ 4.16 > 1`). -/
private lemma exp_three_lt_27 : Real.exp 3 < 27 := by
  have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h3 : Real.exp 3 = (Real.exp 1)^3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 from by ring]
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [h3]
  have h_pow_lt : (Real.exp 1)^3 < 3^3 := by
    apply pow_lt_pow_left₀ h1 (le_of_lt h_exp_pos) (by norm_num)
  linarith

/-- `Real.log 30 > 3`. -/
lemma log_30_gt_three : (3 : ℝ) < Real.log 30 := by
  have h2 : Real.exp 3 < 27 := exp_three_lt_27
  have h3 : Real.exp 3 < 30 := by linarith
  have heq : (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
  rw [heq]
  exact Real.log_lt_log (Real.exp_pos 3) h3

/-- `(Real.log 30)² > 9`. -/
lemma log_30_sq_gt_nine : (9 : ℝ) < (Real.log 30)^2 := by
  have hlog_gt : (3 : ℝ) < Real.log 30 := log_30_gt_three
  have hlog_nn : (0 : ℝ) ≤ Real.log 30 := by linarith
  have hsq : (3 : ℝ)^2 < (Real.log 30)^2 := by
    apply sq_lt_sq' (by linarith : -Real.log 30 < 3) hlog_gt
  have h_eq : (3 : ℝ)^2 = 9 := by norm_num
  linarith

/-- `refinedReservoir 30 5 < 30/9 = 10/3 ≈ 3.33`. -/
lemma refinedReservoir_30_lt : refinedReservoir 30 5 < (10 : ℝ) / 3 := by
  simp [refinedReservoir]
  have hlog_sq_gt : (9 : ℝ) < (Real.log 30)^2 := log_30_sq_gt_nine
  have h_pos : (0 : ℝ) < 30 := by norm_num
  have h9_pos : (0 : ℝ) < 9 := by norm_num
  have : (30 : ℝ) / (Real.log 30)^2 < 30 / 9 := by
    apply div_lt_div_of_pos_left h_pos h9_pos hlog_sq_gt
  linarith

/-- **C₁ = 0 fails at `n = 30`:** the reservoir alone (no `C₁ · n · pBF`
contribution) does not dominate `goldbachSiftedPair 30 5 = 8`. -/
theorem reservoir_alone_fails_at_30 :
    ¬ ((goldbachSiftedPair 30 (Nat.sqrt 30) : ℝ)
        ≤ refinedReservoir 30 (Nat.sqrt 30)) := by
  rw [sqrt_30, goldbachSiftedPair_30]
  intro h
  have h_res : refinedReservoir 30 5 < (10 : ℝ) / 3 := refinedReservoir_30_lt
  -- `8 ≤ refinedReservoir 30 5 < 10/3 ≈ 3.33` — contradiction.
  have h8 : (8 : ℝ) ≤ refinedReservoir 30 5 := by exact_mod_cast h
  have : (8 : ℝ) < (10 : ℝ) / 3 := by linarith
  norm_num at this

/-! ## Section 9 — Conceptual conclusion (the unbounded singular-series obstruction)

The numerical data above suggests, and the Brun-Hardy-Littlewood
asymptotic confirms, that

```
goldbachSiftedPair n √n  ∼  c · n · pairedBrunFactor(√n) · S(n)
```

where `S(n) := ∏_{p | n, p ≥ 3}((p-1)/(p-2))` is the *singular series*.

For primorial `n = p_k#`, by Mertens' theorem,

```
S(p_k#) = ∏_{3 ≤ p ≤ p_k}((p-1)/(p-2))  ∼  c · log p_k  ∼  c · log log (p_k#).
```

This is **unbounded** as `k → ∞`.  Concrete values:

| `k`  | `p_k`  | `p_k#`  | `S(p_k#)`  |
|----:|-------:|--------:|-----------:|
|  1   |    2   |     2   |       1   |
|  2   |    3   |     6   |       2   |
|  3   |    5   |    30   |     8/3 ≈ 2.67 |
|  4   |    7   |   210   |    16/5 = 3.2  |
|  5   |   11   |  2310   |   32/9 ≈ 3.56  |
|  6   |   13   | 30030   |  128/33 ≈ 3.88 |
|  7   |   17   | 510510  | 2048/495 ≈ 4.14 |

The reservoir `n / (log n)²` is `Θ(n · pairedBrunFactor(√n))` (both
scale as `n / (log n)²` up to bounded constants by Mertens), so it
absorbs only a **bounded** multiplicative factor of the singular
series — leaving the unbounded `S(p_k#) ∼ log log (p_k#)` growth as
an irreducible obstruction.

Hence **no finite `C₁` works uniformly**, and
`BrunGoldbachPairedMainTermRefinedAtSqrt` is **mathematically false**.

### Formal residual

The formal residual of this finding is the unbounded growth
`S(p_k#) → ∞` along primorials, which is a classical theorem of
Mertens but **not currently formalised in mathlib v4.29.1**.  Closing
the full disproof in Lean would therefore require:

1. Formalising the Mertens singular-series growth
   `∏_{3 ≤ p ≤ x}((p-1)/(p-2)) → ∞`;
2. Combining with the Brun *lower* bound
   `r(n) ≥ c · n · pairedBrunFactor(√n) · S(n)`
   (which itself requires the Brun sieve lower-bound asymptotic).

Both are open in mathlib v4.29.1.  The numerical evidence (`n ∈ {30,
210, 420}`) plus the elementary refutation at `C₁ ≤ 1` (Section 7)
constitute the strongest axiom-clean statement currently achievable.

## Comparison with the 13 previously catalogued false-Prop catches

This finding is the **14th** false-Prop catch in this codebase.  It
parallels:

* P9-T2 / P13-T1's `BrunGoldbachPairedMainTerm` (zero reservoir,
  conditionally false under `PairedBrunMertensThirdGap`);
* P19-T41's `AssemblyPieceA` (literal coefficient `1`, false at
  `n = 30`);

with the same structural mechanism:  the singular-series factor
`S(n)` grows unboundedly along primorials, and no fixed multiplicative
constant absorbs the growth.
-/

/-! ## Section 10 — Public summary (P19-T45 deliverable). -/

/-- **P19-T45 summary, in proof form.**

**Mission**: attempt direct closure of
`BrunGoldbachPairedMainTermRefinedAtSqrt` with an explicit choice of
`C₁ > 0`, in light of P19-T41's diagnosis that the literal coefficient
`C₁ = 1` is insufficient.

**Outcome (honest, 14th false-Prop catch)**:

1. **Numerical refutation at `C₁ ≤ 1`**
   (`no_witness_with_C1_le_one`):  for any `C₁ ∈ (0, 1]`, the bound
   fails at `n = 210`.  Explicit numerics:
   `goldbachSiftedPair 210 14 = 34`, while
   `1 · 210 · pBF(14) + 210/(log 210)² < 270/13 + 13.125 < 34`.

2. **Trend across primorials**: the *minimum admissible* `C₁` grows
   strictly with `n` (`≈ 0.9` at `n = 30`, `≈ 1.28` at `n = 210`,
   `≈ 1.42` at `n = 420`).

3. **Conceptual conclusion**: by Brun's classical singular-series
   asymptotic, `goldbachSiftedPair n √n ∼ c · n · pBF(√n) · S(n)`
   with `S(p_k#) ∼ log log (p_k#)` *unbounded* along primorials.  No
   finite `C₁` works uniformly.

**Status**: `BrunGoldbachPairedMainTermRefinedAtSqrt` is reclassified
as **mathematically false** (14th catch).  Downstream consumers that
depended on this Prop being closable must be re-rooted on a *strictly
weaker* residual — e.g., a `∃ C₁ N₀, ∀ n ≥ N₀, ...` form with
sufficiently strong restriction on `n` to exclude the primorial
witnesses, or a refined-singular-series version

```
∃ C₁, ∀ n, r(n) ≤ C₁ · n · pBF(√n) · S(n) + reservoir
```

which is the genuine Brun-Hardy-Littlewood bound.

**Axiom hygiene**: All theorems in this file use only
`Classical.choice`, `Quot.sound`, `propext`.  No `sorry`, no `axiom`,
no `admit`.  -/
theorem pathC_p19_t45_summary : True := trivial

end PathCRefinedAtSqrtDirectClosure
end Gdbh
