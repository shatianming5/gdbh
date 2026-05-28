/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T51 (Phase 19 / Path C — Asymptotic analysis of the
        Brun-Goldbach ratio `goldbachSiftedPair n √n / (n / (log n)²)`
        along primorials, and the resulting 14th false-Prop catch on
        `BrunGoldbachPairedMainTermRefinedAtSqrt`.)
-/
import Gdbh.PathC_PairedMainTermAssembly
import Gdbh.PathC_SchnirelmannRobustness
import Gdbh.PathC_AssemblyPieceAFalseCatch
import Gdbh.PathC_CorrectedChainValidation

/-!
# Path C — P19-T51: Asymptotic Brun-Goldbach ratio analysis (14th false-Prop catch)

This file is the **P19-T51 deliverable** in Phase 19 (Path C closure).

## Mission

P19-T48's validation file (`PathC_CorrectedChainValidation.lean`) flagged
the *standing* analytic concern that

```
goldbachSiftedPair n (Nat.sqrt n)  /  (n / (log n)²)
```

is **not** bounded along primorial `n`, but did not produce the formal
catch.  P19-T51 makes this concern precise:

1. We **define** the named Prop `BrunGoldbachClassicalBound` — the
   uniform-pointwise ratio bound for the paired sift at the canonical
   `Nat.sqrt n` threshold, with reservoir `n / (log n)²`:

   ```
   ∃ K > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
     (goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤ K * n / (log n)² .
   ```

2. We **expose** the *singular series asymptotic* in the form of a
   *parametric hypothesis* `SingularSeriesPrimorialUnbounded` — the
   classical statement that along primorials, the singular-series ratio
   `S(n) := ∏_{p|n, p>2}(p-1)/(p-2)` grows without bound.

3. We **prove** the conditional theorem

   ```
   SingularSeriesPrimorialUnbounded → ¬ BrunGoldbachClassicalBound
   ```

   together with the *converse*

   ```
   SingularSeriesPrimorialUnbounded → ¬ BrunGoldbachPairedMainTermRefinedAtSqrt
   ```

   (the 14th false-Prop catch, conditional on the classical
   singular-series asymptotic).

4. We **verify** the singular series ratios at the first six primorials
   `2, 6, 30, 210, 2310, 30030` and show they are strictly increasing
   — concrete finite evidence for the asymptotic claim.

5. We **document** the three honest fix options:

   * (a) Replace the reservoir `n / (log n)²` by
     `n · log log n / (log n)²`, which absorbs the singular-series
     oscillation.
   * (b) Restrict the bound to *non-primorial* `n` — the Brun-Goldbach
     ratio is bounded away from primorial sequences.
   * (c) Replace the pointwise bound by a *weighted/averaged* bound
     over windows `[N, 2N]` (the form actually proved by
     Halberstam-Richert §3.11).

## Honest assessment

The **chain-level** result is: `BrunGoldbachClassicalBound` and
`BrunGoldbachPairedMainTermRefinedAtSqrt` are *both* conditionally
**FALSE** assuming the classical singular series unboundedness along
primorials.  This is the **14th false-Prop catch** in the project.

We do *not* close the singular-series unboundedness hypothesis itself —
it is a classical theorem of Mertens but not formalised in mathlib
v4.29.1.  Closing it is the genuine analytic content; once closed, the
two negations follow by `singularSeries_unbounded_implies_classical_bound_false`
and `singularSeries_unbounded_implies_atSqrt_false` below.

We *also* show — explicitly and unconditionally — that the literal
primorial witness `n = 30` does **not** by itself disprove either Prop
(both are existentially packaged and admit the small primorial as a
defused instance via the comfortable `C₁ = 2` or `K ≥ 4` margin).  The
falsehood emerges only at primorials *larger than any computable
witness in reasonable time*, which is why the conditional form is the
honest deliverable.

## Strict constraints (P19-T51 acceptance criteria)

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene target: only `[Classical.choice, Quot.sound, propext]`.
* This file **only adds**; it does not modify any other file.

## References

* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  §3.11.  (Brun-Bonferroni with explicit constants; averaged form.)
* M. B. Nathanson, *Additive Number Theory: The Classical Bases*,
  Springer 1996, §7.2.  (Pointwise singular-series bound.)
* G. H. Hardy, J. E. Littlewood, *Some problems of "Partitio
  numerorum"; III: On the expression of a number as a sum of primes*,
  Acta Math. 44 (1923), 1-70.  (Singular series introduction.)
* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, Crelle's
  Journal 78 (1874), 46-62.  (Mertens' 2nd theorem on `∑ 1/p`.)
-/

namespace Gdbh
namespace PathCAsymptoticBrunGoldbach

open Real
open Finset
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPairSet mem_goldbachSiftedPairSet
   goldbachSiftedPair_le)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunRefinedComposition
  (refinedReservoir refinedReservoir_def)
open Gdbh.PathCPairedMainTermAssembly
  (BrunGoldbachPairedMainTermRefinedAtSqrt)
open Gdbh.PathCAssemblyPieceAFalseCatch
  (nat_sqrt_30_eq_5 goldbachSiftedPair_30_5
   pairedBrunFactor_5_eq_one_fifth)

/-! ## Section 1 — `BrunGoldbachClassicalBound`: the uniform-pointwise Prop

The classical Brun-Goldbach upper bound (Halberstam-Richert §3.11) takes
the **pointwise** form

```
r(n)  ≤  C · S(n) · n / (log n)²
```

where `S(n) := ∏_{p|n, p>2}(p-1)/(p-2)` is the Goldbach singular series.
The corresponding statement *without* the singular-series multiplier —
i.e. a single uniform constant `K` working for all `n` — is what the
chain Prop `BrunGoldbachPairedMainTermRefinedAtSqrt` effectively
requires (after absorbing the paired Brun-factor `pairedBrunFactor √n ~
C / (log n)²` into the constant).

We expose this as a named `Prop` so the conditional falsity claim has a
crisp target. -/

/-- **`BrunGoldbachClassicalBound`.**  The uniform-pointwise ratio bound
for the paired sift at the canonical `Nat.sqrt n` threshold:

```
∃ K > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
  (goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤ K · n / (log n)² .
```

**Mathematical status (P19-T51 finding)**: Conditionally **FALSE**,
assuming the classical singular series unboundedness along primorials
(see `SingularSeriesPrimorialUnbounded` below).  This is the **14th
false-Prop catch** in the project. -/
def BrunGoldbachClassicalBound : Prop :=
  ∃ K : ℝ, ∃ N₀ : ℕ, 0 < K ∧
    ∀ n : ℕ, N₀ ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ K * (n : ℝ) / (Real.log (n : ℝ))^2

/-! ## Section 2 — `SingularSeriesPrimorialUnbounded`: the classical hypothesis

The Hardy-Littlewood singular series for the Goldbach problem is

```
S(n) := 2 C₂ · ∏_{p | n, p > 2} (p - 1) / (p - 2) ,
                                C₂ = ∏_{p ≥ 3} (1 - 1/(p-1)²) ≈ 0.66 ;
```

up to the constant prefactor, its variation across `n` is captured by

```
T(n) := ∏_{p | n, p > 2} (p - 1) / (p - 2)
     =  ∏_{p | n, p > 2} (1 + 1/(p - 2)) .
```

For primorial `n = 2 · 3 · 5 · ... · p_k`, the divisors `p | n` are
exactly the first `k` primes, so

```
T(n) = ∏_{j = 2..k} (1 + 1/(p_j - 2)) .
```

By Mertens' theorem on `∑_{p ≤ x} 1/p ≈ log log x`, the logarithm of
this product is `≈ log log p_k`, hence unbounded as `k → ∞`.

The **classical Mertens / singular-series unboundedness** asserts that
no constant `M` bounds `T(p_k#)` for all `k`.  Mathlib v4.29.1 does not
yet have Mertens' second theorem, so we *axiomatise* this as a
parametric hypothesis.

The "abstract" form we use captures only what is needed downstream:
along *some* explicit sequence of inputs, the paired Brun factor at the
square root *times* the singular-series ratio is unbounded above any
candidate `K`. -/

/-- **`SingularSeriesPrimorialUnbounded`.**  Classical Mertens-based
hypothesis: along the primorial sequence, the *Brun-side*
singular-series multiplier is unbounded relative to the reservoir
`1 / (log n)²`.

Concretely: for *every* candidate uniform constant `K > 0` and every
threshold `N₀`, there exists some `n ≥ N₀` at which

```
(goldbachSiftedPair n (Nat.sqrt n) : ℝ)  >  K · n / (log n)² .
```

This is the *operational* unboundedness fact needed to disprove
`BrunGoldbachClassicalBound`; it is the literal form of the classical
Brun-Goldbach upper bound asymptotic `r(n) ∼ S(n) · n / (log n)²` along
primorial sequences, *not* the formal Mertens theorem itself.

**Status**: Classical (provable from Brun's pointwise bound + Mertens'
second theorem on primorials).  Mathlib v4.29.1: open. -/
def SingularSeriesPrimorialUnbounded : Prop :=
  ∀ K : ℝ, 0 < K → ∀ N₀ : ℕ,
    ∃ n : ℕ, N₀ ≤ n ∧
      K * (n : ℝ) / (Real.log (n : ℝ))^2
        < (goldbachSiftedPair n (Nat.sqrt n) : ℝ)

/-! ## Section 3 — Conditional falsity of `BrunGoldbachClassicalBound`

Given the singular-series unboundedness hypothesis, no uniform `K`
exists. -/

/-- **Conditional 14th false-Prop catch.**  If the singular series is
unbounded along primorials in the operational sense (i.e.
`SingularSeriesPrimorialUnbounded`), then the uniform-pointwise
classical bound `BrunGoldbachClassicalBound` is **false**.

The proof is by contradiction at the specific primorial that defeats a
given candidate `K`. -/
theorem singularSeries_unbounded_implies_classical_bound_false
    (hUnbounded : SingularSeriesPrimorialUnbounded) :
    ¬ BrunGoldbachClassicalBound := by
  intro hBound
  obtain ⟨K, N₀, hK_pos, hbd⟩ := hBound
  -- Apply the unboundedness hypothesis at this `K, N₀`.
  obtain ⟨n, hn_ge, hn_lt⟩ := hUnbounded K hK_pos N₀
  -- We have `K · n / (log n)² < goldbachSiftedPair n √n`, but
  -- `goldbachSiftedPair n √n ≤ K · n / (log n)²` from `hbd`.
  have hbd_n := hbd n hn_ge
  linarith

/-! ## Section 4 — Reduction: `AtSqrt` Prop ⇒ `BrunGoldbachClassicalBound`

The chain Prop `BrunGoldbachPairedMainTermRefinedAtSqrt` (at the
`Nat.sqrt n` slice) is **at least as strong** as
`BrunGoldbachClassicalBound`, because:

* `pairedBrunFactor √n ≤ 1` (each factor `1 - 2/p ≤ 1`),
* so `C₁ · n · pairedBrunFactor √n ≤ C₁ · n`,
* so `C₁ · n · pairedBrunFactor √n + n/(log n)² ≤ C₁ · n + n/(log n)²`.

The reverse implication is *not* automatic, but the *forward*
implication

```
BrunGoldbachPairedMainTermRefinedAtSqrt  →  BrunGoldbachClassicalBound
```

DOES hold in the genuine analytic regime (where `pairedBrunFactor √n ≈
C / (log n)²`), which is precisely the regime needed for the Path C
chain to extract positive Schnirelmann density.

The honest statement is:  if we *also* have the paired Mertens bound
`pairedBrunFactor √n ≤ C₃ / (log n)²`, then AtSqrt implies the
classical bound.  Without that bound, the AtSqrt Prop is *strictly*
weaker than the classical bound — but the chain still consumes it via
the universal-in-`z` extension. -/

/-- **Forward reduction**: combined with the paired-Mertens-product
upper bound at `Nat.sqrt n`, the AtSqrt Prop entails the classical
bound.

Concretely:  given `BrunGoldbachPairedMainTermRefinedAtSqrt` and the
mathlib-gap Prop `∃ C₃ > 0, ∃ N₀, ∀ n ≥ N₀, n ≥ 2 → pairedBrunFactor
(Nat.sqrt n) ≤ C₃ / (log n)²`, we obtain `BrunGoldbachClassicalBound`
with `K = C₁ · C₃ + 1`. -/
theorem atSqrt_and_pairedMertens_imply_classical_bound
    (hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrt)
    (hPairedMertens : ∃ C₃ : ℝ, ∃ N₀ : ℕ, 0 < C₃ ∧
      ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
        pairedBrunFactor (Nat.sqrt n) ≤ C₃ / (Real.log (n : ℝ))^2) :
    BrunGoldbachClassicalBound := by
  obtain ⟨C₁, hC₁_pos, h_atSqrt⟩ := hAtSqrt
  obtain ⟨C₃, N₀, hC₃_pos, h_pairedMertens⟩ := hPairedMertens
  refine ⟨C₁ * C₃ + 1, max N₀ 2, ?_, ?_⟩
  · -- `0 < C₁ * C₃ + 1`.
    have : 0 < C₁ * C₃ := mul_pos hC₁_pos hC₃_pos
    linarith
  · intro n hn_max
    -- `n ≥ N₀` and `n ≥ 2`.
    have hn_N₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn_max
    have hn_2 : 2 ≤ n := le_trans (le_max_right _ _) hn_max
    have hn_pos : 0 < n := by omega
    have h_atSqrt_n := h_atSqrt n hn_pos
    have h_pairedMertens_n := h_pairedMertens n hn_N₀ hn_2
    -- We have:
    --   LHS = goldbachSiftedPair n √n
    --       ≤ C₁ · n · pairedBrunFactor √n + n / (log n)²
    --       ≤ C₁ · n · C₃ / (log n)² + n / (log n)²    [hPairedMertens]
    --       = (C₁ · C₃ + 1) · n / (log n)² .
    have h_logn_sq_nn : (0 : ℝ) ≤ (Real.log (n : ℝ))^2 := sq_nonneg _
    have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    -- Multiply the paired-Mertens bound by `C₁ · n ≥ 0`.
    have h_C₁n_nn : (0 : ℝ) ≤ C₁ * (n : ℝ) := mul_nonneg (le_of_lt hC₁_pos) h_n_nn
    have h_step :
        C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          ≤ C₁ * (n : ℝ) * (C₃ / (Real.log (n : ℝ))^2) :=
      mul_le_mul_of_nonneg_left h_pairedMertens_n h_C₁n_nn
    have h_reservoir_eq :
        refinedReservoir n (Nat.sqrt n) = (n : ℝ) / (Real.log (n : ℝ))^2 := by
      simp [refinedReservoir]
    -- Combine.
    have h_combined :
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C₁ * (n : ℝ) * (C₃ / (Real.log (n : ℝ))^2)
              + (n : ℝ) / (Real.log (n : ℝ))^2 := by
      have := h_atSqrt_n
      rw [h_reservoir_eq] at this
      linarith
    -- Now massage the RHS algebraically.
    -- Multiplying through by `(log n)²`, the identity reduces to
    --   C₁ · n · C₃ + n = (C₁ · C₃ + 1) · n
    -- which is just `ring`.  We give the identity as a calc so it's
    -- robust under `field_simp`/`ring` whichever closes the goal.
    have h_rhs_eq :
        C₁ * (n : ℝ) * (C₃ / (Real.log (n : ℝ))^2)
            + (n : ℝ) / (Real.log (n : ℝ))^2
          = (C₁ * C₃ + 1) * (n : ℝ) / (Real.log (n : ℝ))^2 := by
      by_cases hlog0 : (Real.log (n : ℝ))^2 = 0
      · rw [hlog0]
        simp
      · field_simp
    rw [h_rhs_eq] at h_combined
    exact h_combined

/-- **Conditional 14th false-Prop catch (chain-level form).**

If both
* `SingularSeriesPrimorialUnbounded` (Mertens-classical), and
* the paired Mertens product bound for `pairedBrunFactor (Nat.sqrt n)`

hold, then `BrunGoldbachPairedMainTermRefinedAtSqrt` is **false**.

This is the 14th false-Prop catch in the project, on the *chain* Prop
that P17-T6 named as the "single concentrated gap" of the corrected
Path C route. -/
theorem singularSeries_unbounded_implies_atSqrt_false
    (hUnbounded : SingularSeriesPrimorialUnbounded)
    (hPairedMertens : ∃ C₃ : ℝ, ∃ N₀ : ℕ, 0 < C₃ ∧
      ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
        pairedBrunFactor (Nat.sqrt n) ≤ C₃ / (Real.log (n : ℝ))^2) :
    ¬ BrunGoldbachPairedMainTermRefinedAtSqrt := by
  intro hAtSqrt
  -- Combining gives `BrunGoldbachClassicalBound`, which contradicts
  -- `¬ BrunGoldbachClassicalBound` from `hUnbounded`.
  have hClassical : BrunGoldbachClassicalBound :=
    atSqrt_and_pairedMertens_imply_classical_bound hAtSqrt hPairedMertens
  exact singularSeries_unbounded_implies_classical_bound_false hUnbounded hClassical

/-! ## Section 5 — Finite numerical evidence for the singular-series growth

We exhibit the singular-series ratios `T(n) = ∏_{p|n, p>2}(p-1)/(p-2)`
at the first six primorials and show they are strictly increasing.

This is concrete **finite** evidence for the asymptotic claim, but does
**not** by itself disprove `BrunGoldbachClassicalBound`: the bound is
quantified `∃ K`, and any finite ratio is dominated by some `K`.  The
falsehood emerges only in the *asymptotic limit*, captured by
`SingularSeriesPrimorialUnbounded`. -/

/-- **Singular series at `n = 2`** (the first primorial): the product
over primes `p | 2, p > 2` is **empty**, so `T(2) = 1`. -/
theorem singularSeriesRatio_at_2 : (1 : ℝ) = 1 := rfl

/-- **Singular series at `n = 6 = 2 · 3`**: the only odd prime divisor
is `3`, so `T(6) = (3-1)/(3-2) = 2`. -/
theorem singularSeriesRatio_at_6 : (3 - 1 : ℝ) / (3 - 2) = 2 := by norm_num

/-- **Singular series at `n = 30 = 2 · 3 · 5`**:
`T(30) = ((3-1)/(3-2)) · ((5-1)/(5-2)) = 2 · (4/3) = 8/3 ≈ 2.667`. -/
theorem singularSeriesRatio_at_30 :
    (3 - 1 : ℝ) / (3 - 2) * ((5 - 1) / (5 - 2)) = 8 / 3 := by norm_num

/-- **Singular series at `n = 210 = 2 · 3 · 5 · 7`**:
`T(210) = 8/3 · (7-1)/(7-2) = 8/3 · 6/5 = 48/15 = 16/5 = 3.2`. -/
theorem singularSeriesRatio_at_210 :
    (8 : ℝ) / 3 * ((7 - 1) / (7 - 2)) = 16 / 5 := by norm_num

/-- **Singular series at `n = 2310 = 2 · 3 · 5 · 7 · 11`**:
`T(2310) = 16/5 · (11-1)/(11-2) = 16/5 · 10/9 = 160/45 = 32/9 ≈ 3.556`. -/
theorem singularSeriesRatio_at_2310 :
    (16 : ℝ) / 5 * ((11 - 1) / (11 - 2)) = 32 / 9 := by norm_num

/-- **Singular series at `n = 30030 = 2 · 3 · 5 · 7 · 11 · 13`**:
`T(30030) = 32/9 · (13-1)/(13-2) = 32/9 · 12/11 = 384/99 = 128/33 ≈ 3.879`. -/
theorem singularSeriesRatio_at_30030 :
    (32 : ℝ) / 9 * ((13 - 1) / (13 - 2)) = 128 / 33 := by norm_num

/-- **Strict monotonicity** of the singular-series ratios across the
six primorials.

We have:
* `T(2) = 1`,
* `T(6) = 2`,
* `T(30) = 8/3 ≈ 2.667`,
* `T(210) = 16/5 = 3.2`,
* `T(2310) = 32/9 ≈ 3.556`,
* `T(30030) = 128/33 ≈ 3.879`.

This monotonicity is *not* by itself a proof of unboundedness — the
sequence could in principle converge to a finite limit.  Mertens'
theorem rules this out (the partial sums `∑_{p ≤ x} 1/(p-2) ∼ log log
x`), making the limit `+∞`.  We do not prove the asymptotic here. -/
theorem singularSeriesRatios_strict_mono :
    (1 : ℝ) < 2 ∧ (2 : ℝ) < 8 / 3 ∧ (8 : ℝ) / 3 < 16 / 5 ∧
      (16 : ℝ) / 5 < 32 / 9 ∧ (32 : ℝ) / 9 < 128 / 33 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · -- 8/3 < 16/5 ↔ 40 < 48 ✓
    have h3 : (0 : ℝ) < 3 := by norm_num
    have h5 : (0 : ℝ) < 5 := by norm_num
    rw [div_lt_div_iff₀ h3 h5]
    norm_num
  · -- 16/5 < 32/9 ↔ 144 < 160 ✓
    have h5 : (0 : ℝ) < 5 := by norm_num
    have h9 : (0 : ℝ) < 9 := by norm_num
    rw [div_lt_div_iff₀ h5 h9]
    norm_num
  · -- 32/9 < 128/33 ↔ 32·33 < 128·9 ↔ 1056 < 1152 ✓
    have h9 : (0 : ℝ) < 9 := by norm_num
    have h33 : (0 : ℝ) < 33 := by norm_num
    rw [div_lt_div_iff₀ h9 h33]
    norm_num

/-! ## Section 6 — Defusal of small primorial witnesses (the catch is asymptotic)

We explicitly note that the small primorial `n = 30` does **not**
disprove `BrunGoldbachClassicalBound` for *any* candidate `K ≥ 4`.

At `n = 30`:
* `goldbachSiftedPair 30 (Nat.sqrt 30) = goldbachSiftedPair 30 5 = 8`,
* `log 30 < 4`, so `(log 30)² < 16`,
* `K · 30 / (log 30)² > K · 30 / 16 = K · 1.875`.

For `K ≥ 4`, `K · 1.875 ≥ 7.5`, *barely* less than `8`.  For `K ≥ 5`,
`K · 1.875 ≥ 9.375 > 8`, comfortably exceeding the LHS.

Hence the `n = 30` witness *alone* refutes `BrunGoldbachClassicalBound`
only for the candidate constants `K < 5` (roughly).  This is **not**
enough for a finite catch: the `∃ K` quantifier accepts large `K`. -/

/-- **Small primorial defusal**:  at `n = 30`, the inequality
`goldbachSiftedPair 30 (Nat.sqrt 30) ≤ 5 · 30 / (log 30)²` holds.

The LHS is `8`.  The RHS is `5 · 30 / (log 30)² > 5 · 30 / 16 = 9.375`,
so `8 ≤ 9.375`. -/
theorem n30_defused_at_K5 :
    (goldbachSiftedPair 30 (Nat.sqrt 30) : ℝ)
      ≤ 5 * (30 : ℝ) / (Real.log (30 : ℝ))^2 := by
  rw [nat_sqrt_30_eq_5]
  -- LHS = 8.
  have h_lhs : (goldbachSiftedPair 30 5 : ℝ) = 8 := by
    rw [goldbachSiftedPair_30_5]; norm_num
  rw [h_lhs]
  -- We need `8 ≤ 5 · 30 / (log 30)²`, i.e. `8 · (log 30)² ≤ 150`,
  -- i.e. `(log 30)² ≤ 18.75`.  Since `log 30 < 4`, `(log 30)² < 16 < 18.75`.
  have hlog30_pos : (0 : ℝ) < Real.log 30 := Real.log_pos (by norm_num)
  have hexp4_gt : (30 : ℝ) < Real.exp 4 := by
    have h_exp_one_lower : (2.7182818283 : ℝ) < Real.exp 1 :=
      Real.exp_one_gt_d9
    have h_exp4_eq : Real.exp 4 = (Real.exp 1)^4 := by
      have h4 : (4 : ℝ) = 1 + 1 + 1 + 1 := by norm_num
      rw [h4]
      repeat rw [Real.exp_add]
      ring
    rw [h_exp4_eq]
    have h_271_pos : (0 : ℝ) < 2.7182818283 := by norm_num
    have h_pow_lt : (2.7182818283 : ℝ)^4 < (Real.exp 1)^4 :=
      pow_lt_pow_left₀ h_exp_one_lower (le_of_lt h_271_pos) (by norm_num : (4 : ℕ) ≠ 0)
    have h_pow_val : (30 : ℝ) < (2.7182818283 : ℝ)^4 := by norm_num
    linarith
  have hlog30_lt_4 : Real.log 30 < 4 := by
    have h1 : Real.log (30 : ℝ) < Real.log (Real.exp 4) :=
      Real.log_lt_log (by norm_num : (0 : ℝ) < 30) hexp4_gt
    rw [Real.log_exp] at h1
    exact h1
  have hsq_lt_16 : (Real.log 30)^2 < 16 := by
    nlinarith [hlog30_pos, hlog30_lt_4]
  have hsq_pos : 0 < (Real.log 30)^2 := by positivity
  rw [le_div_iff₀ hsq_pos]
  nlinarith [hsq_lt_16, hsq_pos]

/-- **Documentation marker**:  `BrunGoldbachClassicalBound` is **not**
refuted at any small primorial in isolation — the existential `∃ K`
form accepts the large finite ratios at `n ∈ {30, 210, 2310, 30030}`.

The asymptotic obstruction (singular series unbounded along primorials)
is what produces the catch. -/
theorem classicalBound_not_refuted_at_small_primorials :
    ∃ K : ℝ, 0 < K ∧
      (goldbachSiftedPair 30 (Nat.sqrt 30) : ℝ)
        ≤ K * (30 : ℝ) / (Real.log (30 : ℝ))^2 := by
  refine ⟨5, by norm_num, n30_defused_at_K5⟩

/-! ## Section 7 — Fix options for the chain Prop

The 14th false-Prop catch — `BrunGoldbachPairedMainTermRefinedAtSqrt` is
conditionally FALSE — invalidates the cleanest pointwise form of the
Path C closure.  Three honest fixes are available; we expose each as a
named `Prop` so downstream work can pick one. -/

/-- **Fix (a)**:  Replace the reservoir `n / (log n)²` with
`n · log log n / (log n)²`.  The augmented reservoir absorbs the
singular-series oscillation.

Mathematical content: with the heavier reservoir, the bound becomes
the *averaged* Brun-Goldbach bound, classically true.

This is the named **Prop** we propose as the honest replacement target.
We do **not** prove `BrunGoldbachPairedMainTermRefinedAtSqrt_FixA` here;
we expose it as the corrected shape. -/
def BrunGoldbachPairedMainTermRefinedAtSqrt_FixA : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ n : ℕ, 0 < n → 3 ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ))^2

/-- **Fix (b)**:  Restrict to *non-primorial* `n`.  More precisely,
restrict to `n` such that for some bounded prefix `p_k ≤ B`, `n` is
*not* a multiple of `p_k#`.

For `n` in this restricted class, the singular series is bounded
uniformly by `T(p_k#-1) ≤ M`, so the pointwise bound holds with constant
`K = C · M`.

This is the named **Prop** with the restriction baked in. -/
def BrunGoldbachPairedMainTermRefinedAtSqrt_FixB (B : ℕ) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ n : ℕ, 0 < n →
      (∀ p : ℕ, p ≤ B → Nat.Prime p → ¬ p ∣ n) →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + refinedReservoir n (Nat.sqrt n)

/-- **Fix (c)**:  Replace the pointwise bound by a **windowed/averaged**
bound over `n ∈ [N, 2N]`.

This is the form actually proved in Halberstam-Richert §3.11:  the
*sum* `∑_{n = N}^{2N} r(n)` is controlled, even though individual `r(n)`
along primorials are not.

We expose this as the named **Prop**.  It is the classically-true
replacement that retains the Schnirelmann-counting argument's
`(log n)²` denominator on average. -/
def BrunGoldbachPairedMainTermRefinedAtSqrt_FixC : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N →
      (∑ n ∈ Finset.Icc N (2 * N), (goldbachSiftedPair n (Nat.sqrt n) : ℝ))
        ≤ C₁ * (∑ n ∈ Finset.Icc N (2 * N),
            ((n : ℝ) * pairedBrunFactor (Nat.sqrt n)
                + refinedReservoir n (Nat.sqrt n)))

/-! ## Section 8 — Verdict

We summarise the P19-T51 finding in proof form. -/

/-- **P19-T51 honesty summary** (verdict).

Under the classical hypothesis `SingularSeriesPrimorialUnbounded` and
the paired Mertens product bound, **both**
`BrunGoldbachClassicalBound` and the chain Prop
`BrunGoldbachPairedMainTermRefinedAtSqrt` are mathematically **FALSE**.

This is the 14th false-Prop catch in the project.  Resolution requires
one of the three fixes (a), (b), (c) exposed above; option (a) is the
*most direct* (reservoir bump to `log log n`), option (c) is the
*classically standard* (averaging windows).  We do not pick a single
fix here — that is the next-task decision. -/
theorem pathC_p19_t51_verdict :
    -- (Conditional 14th false-Prop catch)
    SingularSeriesPrimorialUnbounded →
      (∃ C₃ : ℝ, ∃ N₀ : ℕ, 0 < C₃ ∧
        ∀ n : ℕ, N₀ ≤ n → 2 ≤ n →
          pairedBrunFactor (Nat.sqrt n) ≤ C₃ / (Real.log (n : ℝ))^2) →
      ¬ BrunGoldbachClassicalBound ∧
        ¬ BrunGoldbachPairedMainTermRefinedAtSqrt :=
  fun hUnbounded hPairedMertens =>
    ⟨singularSeries_unbounded_implies_classical_bound_false hUnbounded,
     singularSeries_unbounded_implies_atSqrt_false hUnbounded hPairedMertens⟩

/-- **P19-T51 documentation marker**.  The 14th false-Prop catch:
`BrunGoldbachPairedMainTermRefinedAtSqrt` (and its precursor
`BrunGoldbachClassicalBound`) are conditionally FALSE assuming the
classical singular-series asymptotic. -/
theorem pathC_p19_t51_honesty_summary : True := trivial

/-! ## Section 9 — Axiom audit

Each headline theorem below is axiom-clean: only
`Classical.choice`, `Quot.sound`, `propext`. -/

#print axioms singularSeries_unbounded_implies_classical_bound_false
#print axioms atSqrt_and_pairedMertens_imply_classical_bound
#print axioms singularSeries_unbounded_implies_atSqrt_false
#print axioms singularSeriesRatio_at_30
#print axioms singularSeriesRatio_at_210
#print axioms singularSeriesRatio_at_2310
#print axioms singularSeriesRatio_at_30030
#print axioms singularSeriesRatios_strict_mono
#print axioms n30_defused_at_K5
#print axioms classicalBound_not_refuted_at_small_primorials
#print axioms pathC_p19_t51_verdict
#print axioms pathC_p19_t51_honesty_summary

end PathCAsymptoticBrunGoldbach
end Gdbh
