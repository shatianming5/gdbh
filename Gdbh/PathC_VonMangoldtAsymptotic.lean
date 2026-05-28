/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P15-T1 (Phase 15 / Path C — `VonMangoldtSumLogN` decomposition)
-/
import Gdbh.PathC_MertensFirstProof
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Path C — Von Mangoldt asymptotic `Σ Λ(n)/n = log N + O(1)` decomposition (P15-T1)

This file is the **P15-T1 deliverable** in Phase 15.  Its target is the
named open `Prop` `Gdbh.PathCMertensFirstProof.VonMangoldtSumLogN`:

```
∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
  |(∑ n ∈ Icc 1 N, Λ n / n) - log N| ≤ C .
```

This is the Chebyshev-Mertens identity for the von Mangoldt-divided-by-id
sum, and the deepest analytic atom of the Mertens 1st proof chain.

## Strategy — classical Chebyshev–Stirling identity

We decompose `VonMangoldtSumLogN` into four strictly smaller named open
`Prop`s, three of which are closeable axiom-cleanly *in this session*
(using mathlib's `Stirling.le_log_factorial_stirling`,
`Chebyshev.psi_le_const_mul_self`, and the divisor-sum identity
`ArithmeticFunction.vonMangoldt_sum : ∑_{d ∣ n} Λ(d) = log n`).

The Chebyshev derivation is the following identity chain, valid for any
`N ≥ 1`:

```
                       (1) divisor-sum identity:     Σ_d Λ(d)·⌊N/d⌋ = Σ_n log n = log(N!)
                       (2) split:                    Σ_d Λ(d)·(N/d) = Σ_d Λ(d)·⌊N/d⌋ + Σ_d Λ(d)·{N/d}
                       (3) ⟹                         N·Σ_d Λ(d)/d   = log(N!) + Σ_d Λ(d)·{N/d}
                       (4) Stirling:                 log(N!) = N·log N − N + O(log N)
                       (5) fractional bound:         |Σ_d Λ(d)·{N/d}| ≤ ψ(N) ≤ C·N
                       (6) divide by N:              Σ_d Λ(d)/d − log N = −1 + O((log N)/N) + O(1)
```

Thus `Σ Λ(d)/d = log N + O(1)`.  ✓

## Named sub-Props

1. **`FactorialLogIdentity`** — `Σ_{n ∈ Icc 1 N} log n = log (N!)`.
   *Pure rearrangement* (`log_prod` over `Finset.Icc 1 N`).  **Closed
   axiom-clean in this file**.

2. **`LogFactorialVonMangoldtIdentity`** — for every `N`,
   `Σ_{d ∈ Icc 1 N} Λ(d) · ⌊N/d⌋ = Σ_{n ∈ Icc 1 N} log n`.
   The classical Chebyshev identity, derivable from
   `ArithmeticFunction.vonMangoldt_sum` (mathlib) by re-indexing.
   *Open* — left as a named gap (re-indexing `(n, d) : d ∣ n` with
   `⌊N/d⌋` count of multiples).

3. **`LogFactorialStirlingBound`** — `∃ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
   |log (N!) − N · log N + N| ≤ C · (log N + 1)`.  Mathlib provides
   the **lower** half (`Stirling.le_log_factorial_stirling`); the
   **upper** half is `log(N!) ≤ N · log N`, immediate from
   `Nat.factorial_le_pow` and `log_le_log`.  *Open* — left as a named
   gap (need to assemble both halves into the symmetric bound).

4. **`FractionalPartVonMangoldtBound`** — `∃ C' : ℝ, ∀ N : ℕ,
   |Σ_d Λ(d) · ({N/d : ℝ})| ≤ C' · N`.  The fractional part lies in
   `[0, 1)`, so the sum is `≤ Σ_{d ≤ N} Λ(d) = ψ(N) ≤ C·N`
   (`Chebyshev.psi_le_const_mul_self`).  **Closed axiom-clean in this
   file**.

## Mechanical assembly bridge

Given all four sub-Props, `VonMangoldtSumLogN` follows by the algebra:

```
|Σ_d Λ(d)/d − log N|
  = |(log(N!) + frac sum)/N − log N|                (× by N: identity (3))
  = (1/N) · |log(N!) − N · log N + frac sum|
  ≤ (1/N) · (|log(N!) − N · log N + N| + |frac sum| + N)
  ≤ (1/N) · (C · (log N + 1) + C' · N + N)
  = O((log N)/N) + C' + 1 ≤ C' + 2  (for N large).
```

`mertensFirstTheoremBound_via_vonMangoldt_components` discharges
`MertensFirstTheoremBound` from the *three* gaps
`LogFactorialVonMangoldtIdentity + LogFactorialStirlingBound +
PrimePowerTailBound`, by combining `vonMangoldtSumLogN_of_components`
with `mertensFirstTheoremBound_of_components` from
`PathC_MertensFirstProof`.

## What's closed vs. open in this file

**Closed axiom-clean (only `Classical.choice, Quot.sound, propext`)**:

* `factorialLogIdentity_holds` — `Σ_{n ∈ Icc 1 N} log n = log (N!)`.
* `fractionalPartVonMangoldtBound_holds` — the fractional-part bound.
* `vonMangoldtSumLogN_of_components` — the mechanical assembly bridge.
* `vonMangoldtSumLogN_of_three_gaps` — full chain with `factorialLog`
   and `fractionalPart` discharged.
* `mertensFirstTheoremBound_via_vonMangoldt_components` — end-to-end:
  `LogFactorialVonMangoldtIdentity + LogFactorialStirlingBound +
   PrimePowerTailBound ⇒ MertensFirstTheoremBound`.

**Open (named gaps, *strictly smaller* than `VonMangoldtSumLogN`)**:

* `LogFactorialVonMangoldtIdentity` — the classical Chebyshev identity
  `Σ_d Λ(d) · ⌊N/d⌋ = log(N!)`.  Provable axiom-cleanly from
  `vonMangoldt_sum` (mathlib) via a re-indexing of divisor pairs;
  left here as a named gap.
* `LogFactorialStirlingBound` — symmetric two-sided Stirling bound.
  The lower half `le_log_factorial_stirling` is in mathlib; the upper
  `log(N!) ≤ N · log N` is immediate from `factorial_le_pow`; gap is
  the *symmetric assembly* with the `−N` shift.

## Axiom budget

All theorems below are axiom-clean: only
`Classical.choice, Quot.sound, propext`.

## References

* P. Chebyshev, *Mémoire sur les nombres premiers* (1850).
* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, 1874.
* G. H. Hardy, E. M. Wright, *Theory of Numbers*, §22.7.
* T. Tao, *Analytic Prime Number Theory*, Theorem 1.10.
-/

namespace Gdbh
namespace PathCVonMangoldtAsymptotic

open Real Finset
open ArithmeticFunction
open Gdbh.PathCMertensSecondProof
open Gdbh.PathCMertensFirstProof

/-! ## Section 1 — Named open sub-Props -/

/-- **Sub-Prop 1**: `Σ_{n ∈ Icc 1 N} log n = log (N!)`.

A pure rearrangement: `log` of a product equals the sum of logs, and
`N! = ∏_{n ∈ Icc 1 N} n` is the standard product representation of the
factorial.  Equivalently, `log (N!)` defined via the natural cast.

(This `Prop` is closed in this file.) -/
def FactorialLogIdentity : Prop :=
  ∀ N : ℕ,
    (∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ)) = Real.log ((Nat.factorial N : ℕ) : ℝ)

/-- **Sub-Prop 2**: the *Chebyshev–von Mangoldt identity*.

```
∀ N : ℕ, Σ_{d ∈ Icc 1 N} Λ(d) · ⌊N/d⌋ = Σ_{n ∈ Icc 1 N} log n .
```

This is the classical identity behind Chebyshev's `ψ` analysis.
Derivable axiom-cleanly from `ArithmeticFunction.vonMangoldt_sum :
∑_{d ∣ n} Λ(d) = log n` (mathlib) by swapping order of summation:

```
Σ_{n ≤ N} log n  =  Σ_{n ≤ N} Σ_{d ∣ n} Λ(d)
                =  Σ_{d ≤ N} Λ(d) · |{n ≤ N : d ∣ n}|
                =  Σ_{d ≤ N} Λ(d) · ⌊N/d⌋ .
```

(Left as a named open gap in this file — re-indexing technicality.) -/
def LogFactorialVonMangoldtIdentity : Prop :=
  ∀ N : ℕ,
    (∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ))
      = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ)

/-- **Sub-Prop 3**: *symmetric Stirling bound* on `log (N!)`.

```
∃ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
  |log (N!) − N · log N + N|  ≤  C · (log N + 1) .
```

Lower half (mathlib v4.29.1):
`Stirling.le_log_factorial_stirling` —
`N log N − N + log N / 2 + log(2π)/2 ≤ log (N!)`.

Upper half (elementary):  `N! ≤ N^N` ⟹ `log (N!) ≤ N · log N`.

Combining gives the symmetric bound with leading error `O(log N)`.
(Left as a named open gap in this file — assembly only.) -/
def LogFactorialStirlingBound : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + (N : ℝ)|
      ≤ C * (Real.log (N : ℝ) + 1)

/-- **Sub-Prop 4**: *fractional-part von Mangoldt bound*.

```
∃ C' : ℝ, ∀ N : ℕ,
  |Σ_{d ∈ Icc 1 N} Λ(d) · ((N : ℝ)/d − ⌊N/d⌋)|  ≤  C' · N .
```

The fractional part `{N/d} := N/d − ⌊N/d⌋ ∈ [0, 1)`, so

```
0 ≤ Σ_{d ≤ N} Λ(d) · {N/d}  ≤  Σ_{d ≤ N} Λ(d) · 1  =  ψ(N)  ≤  (log 4 + 4) · N .
```

This is `Chebyshev.psi_le_const_mul_self` (mathlib v4.29.1).

(This `Prop` is closed in this file.) -/
def FractionalPartVonMangoldtBound : Prop :=
  ∃ C' : ℝ, 0 ≤ C' ∧ ∀ N : ℕ,
    |∑ d ∈ Finset.Icc 1 N,
        Λ d * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))| ≤ C' * (N : ℝ)

/-! ## Section 2 — Closed sub-Prop: `FactorialLogIdentity` -/

/-- **Closure** of `FactorialLogIdentity`.  Pure rearrangement: by
induction on `N`, using `factorial_succ` and `log_mul`.

For `N = 0` both sides are `0` (empty sum; `log 1 = 0`).  For the
inductive step:

```
log ((N+1)!) = log ((N+1) · N!) = log (N+1) + log (N!)
             = log (N+1) + Σ_{n ∈ Icc 1 N} log n
             = Σ_{n ∈ Icc 1 (N+1)} log n .
```

(Closed axiom-clean.) -/
theorem factorialLogIdentity_holds : FactorialLogIdentity := by
  intro N
  induction N with
  | zero =>
      simp [Nat.factorial_zero]
  | succ k ih =>
      -- Σ_{n ∈ Icc 1 (k+1)} log n = log (k+1) + Σ_{n ∈ Icc 1 k} log n
      have hsum :
          (∑ n ∈ Finset.Icc 1 (k + 1), Real.log (n : ℝ))
            = Real.log ((k + 1 : ℕ) : ℝ)
                + ∑ n ∈ Finset.Icc 1 k, Real.log (n : ℝ) := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk
          simp
        · -- For k ≥ 1, Icc 1 (k+1) = insert (k+1) (Icc 1 k).
          have hnot : (k + 1) ∉ Finset.Icc 1 k := by
            simp
          have hicc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
            ext n; simp [Finset.mem_Icc, Finset.mem_insert]
            omega
          rw [hicc, Finset.sum_insert hnot]
      -- factorial recursion: (k+1)! = (k+1) · k!.
      have hfact : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k :=
        Nat.factorial_succ k
      have hk_real_pos : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
      have hfact_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by
        exact_mod_cast Nat.factorial_pos k
      have hlog_mul :
          Real.log (((k + 1) * Nat.factorial k : ℕ) : ℝ)
            = Real.log ((k + 1 : ℕ) : ℝ) + Real.log ((Nat.factorial k : ℕ) : ℝ) := by
        push_cast
        exact Real.log_mul hk_real_pos.ne' hfact_pos.ne'
      rw [hsum, ih, hfact, hlog_mul]

/-! ## Section 3 — Closed sub-Prop: `FractionalPartVonMangoldtBound` -/

/-- For `1 ≤ d ≤ N`, the fractional part `(N : ℝ)/d − ⌊N/d⌋ ∈ [0, 1)`. -/
lemma fract_div_le_one {N d : ℕ} (hd : 1 ≤ d) :
    (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) < 1 ∧
    0 ≤ (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨?_, ?_⟩
  · -- N/d - ⌊N/d⌋ < 1  ⟺  N/d < ⌊N/d⌋ + 1.
    -- Use Nat.div_add_mod: N = d * (N/d) + N%d, with N%d < d.
    have hdiv_mod : N = d * (N / d) + N % d := (Nat.div_add_mod N d).symm
    have hmod_lt : N % d < d := Nat.mod_lt N hd
    -- So N < d * (N/d) + d, hence N < d * (N/d + 1).
    have hN_lt_nat : N < d * (N / d) + d := by omega
    have hN_lt : (N : ℝ) < (d : ℝ) * ((N / d : ℕ) : ℝ) + (d : ℝ) := by
      have : ((N : ℕ) : ℝ) < ((d * (N / d) + d : ℕ) : ℝ) := by exact_mod_cast hN_lt_nat
      simpa [Nat.cast_mul, Nat.cast_add] using this
    have hsplit : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd_pos]; nlinarith
    linarith
  · -- 0 ≤ N/d - ⌊N/d⌋  ⟺  ⌊N/d⌋ * d ≤ N.
    have hnat : (N / d) * d ≤ N := Nat.div_mul_le_self N d
    have : (((N / d : ℕ) * d : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnat
    have hcast : (((N / d : ℕ) * d : ℕ) : ℝ) = ((N / d : ℕ) : ℝ) * (d : ℝ) := by
      push_cast; ring
    rw [hcast] at this
    have : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hd_pos]; exact this
    linarith

/-- The sum `Σ_d Λ(d) · {N/d}` over `d ∈ Icc 1 N` is bounded by `ψ(N)`.

For each `d ∈ Icc 1 N`:
* `Λ(d) ≥ 0` (`vonMangoldt_nonneg`),
* `0 ≤ {N/d} < 1` (`fract_div_le_one`),
so `Λ(d) · {N/d} ≤ Λ(d) · 1 = Λ(d)`.  Summing: `Σ ≤ Σ_{d ≤ N} Λ(d) = ψ(N)`. -/
lemma fractional_part_sum_le_psi (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        Λ d * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ)))
      ≤ Chebyshev.psi ((N : ℕ) : ℝ) := by
  -- Step 1: pointwise bound Λ(d) * {N/d} ≤ Λ(d).
  have hpt : ∀ d ∈ Finset.Icc 1 N,
      Λ d * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ)) ≤ Λ d := by
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, _⟩
    have ⟨hfrac_lt, hfrac_nn⟩ := fract_div_le_one (N := N) hd1
    have hΛnn : 0 ≤ Λ d := vonMangoldt_nonneg
    -- Λ d * frac ≤ Λ d * 1 = Λ d.
    calc Λ d * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))
        ≤ Λ d * 1 := by
          apply mul_le_mul_of_nonneg_left _ hΛnn
          linarith
      _ = Λ d := by ring
  -- Step 2: sum the pointwise bound.
  have hsum_le : (∑ d ∈ Finset.Icc 1 N,
        Λ d * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ)))
      ≤ ∑ d ∈ Finset.Icc 1 N, Λ d :=
    Finset.sum_le_sum hpt
  -- Step 3: identify Σ_{d ∈ Icc 1 N} Λ d with ψ((N : ℝ)).
  -- ψ((N : ℝ)) = Σ_{d ∈ Ioc 0 ⌊N⌋₊} Λ d = Σ_{d ∈ Ioc 0 N} Λ d = Σ_{d ∈ Icc 1 N} Λ d.
  have hpsi_eq : Chebyshev.psi ((N : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, Λ d := by
    unfold Chebyshev.psi
    -- ⌊(N : ℝ)⌋₊ = N for N : ℕ.
    rw [Nat.floor_natCast]
    -- Ioc 0 N = Icc 1 N (as Finsets of naturals).
    have hset : (Finset.Ioc 0 N : Finset ℕ) = Finset.Icc 1 N := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hset]
  rw [hpsi_eq]; exact hsum_le

/-- **Closure** of `FractionalPartVonMangoldtBound`.  Take
`C' := log 4 + 4` (the constant from `Chebyshev.psi_le_const_mul_self`).

For every `N : ℕ`:
* Each term `Λ(d) · {N/d} ≥ 0` (both factors are nonneg).
* `Σ ≤ ψ((N : ℝ)) ≤ (log 4 + 4) · N` by `psi_le_const_mul_self`.

(Closed axiom-clean.) -/
theorem fractionalPartVonMangoldtBound_holds : FractionalPartVonMangoldtBound := by
  refine ⟨Real.log 4 + 4, ?_, ?_⟩
  · -- 0 ≤ log 4 + 4
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  intro N
  -- Set S := Σ_d Λ(d) * {N/d}.  Show 0 ≤ S ≤ (log 4 + 4) * N, so |S| ≤ (log 4 + 4) * N.
  set S := (∑ d ∈ Finset.Icc 1 N,
      Λ d * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))) with hS
  -- 0 ≤ S
  have hS_nonneg : 0 ≤ S := by
    refine Finset.sum_nonneg ?_
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, _⟩
    have ⟨_, hfrac_nn⟩ := fract_div_le_one (N := N) hd1
    exact mul_nonneg vonMangoldt_nonneg hfrac_nn
  -- S ≤ ψ(N) ≤ (log 4 + 4) * N.
  have hS_le_psi : S ≤ Chebyshev.psi ((N : ℕ) : ℝ) :=
    fractional_part_sum_le_psi N
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  have hpsi_le : Chebyshev.psi ((N : ℕ) : ℝ) ≤ (Real.log 4 + 4) * (N : ℝ) :=
    Chebyshev.psi_le_const_mul_self hN_nn
  have hS_le : S ≤ (Real.log 4 + 4) * (N : ℝ) := le_trans hS_le_psi hpsi_le
  -- |S| = S ≤ bound.
  rw [abs_of_nonneg hS_nonneg]; exact hS_le

/-! ## Section 4 — Mechanical assembly bridge -/

/-- **Mechanical assembly**: `VonMangoldtSumLogN` follows from the four
named sub-Props by the Chebyshev identity chain.

Reasoning (sketched in the file header):

Given the identity
```
N · Σ_d Λ(d)/d = Σ_d Λ(d) · ⌊N/d⌋ + Σ_d Λ(d) · {N/d}
              = log (N!) + (frac sum) ,
```
divide by `N`:
```
Σ_d Λ(d)/d − log N = (log(N!) − N·log N + (frac sum))/N
                   = (log(N!) − N·log N + N)/N + ((frac sum) − N)/N
```
Use Stirling for the first quotient (size `≤ C·(log N + 1)/N`, → 0)
and the fractional bound for the second (size `≤ C' + 1`, uniformly).

We get `|Σ Λ(d)/d − log N| ≤ C · (log N + 1)/N + C' + 1 ≤ C' + 2` for
`N ≥ N₀'` large enough.

(Closed axiom-clean.) -/
theorem vonMangoldtSumLogN_of_components
    (hId : LogFactorialVonMangoldtIdentity)
    (hFL : FactorialLogIdentity)
    (hStir : LogFactorialStirlingBound)
    (hFrac : FractionalPartVonMangoldtBound) :
    VonMangoldtSumLogN := by
  obtain ⟨C, N₀, hStirBnd⟩ := hStir
  obtain ⟨C', hC'_nn, hFracBnd⟩ := hFrac
  -- Choose final witnesses.
  -- For N ≥ max N₀ 1, we will show |Σ Λ(d)/d − log N| ≤ C + C' + 1.
  refine ⟨C + C' + 1, max N₀ 1, ?_⟩
  intro N hN
  have hN_ge_N₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN_ge_1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_ge_1
  -- Identity (3): N · Σ Λ(d)/d = log(N!) + (frac sum).
  -- Step 1: Σ_d Λ(d) * (N/d) = Σ_d Λ(d) * ⌊N/d⌋ + Σ_d Λ(d) * {N/d}.
  -- We translate everything in terms of (Λ d / d) so as to compare with VonMangoldtSumLogN.
  -- Concretely: for d ∈ Icc 1 N (so d ≥ 1, hence d > 0),
  --   Λ(d) * (N/d) = N * (Λ(d)/d)
  --   Λ(d) * ⌊N/d⌋ + Λ(d) * (N/d − ⌊N/d⌋) = Λ(d) * (N/d).
  -- Hence: N * (Λ(d)/d) = Λ(d) * ⌊N/d⌋ + Λ(d) * {N/d}.
  have hpt :
      ∀ d ∈ Finset.Icc 1 N,
        (N : ℝ) * (Λ d / (d : ℝ))
          = Λ d * ((N / d : ℕ) : ℝ)
              + Λ d * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ)) := by
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, _⟩
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    field_simp
    ring
  -- Sum the pointwise identity.
  have hsum_id :
      ∑ d ∈ Finset.Icc 1 N, (N : ℝ) * (Λ d / (d : ℝ))
        = (∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ))
          + ∑ d ∈ Finset.Icc 1 N,
              Λ d * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpt
  -- Pull out N from LHS.
  have hLHS :
      ∑ d ∈ Finset.Icc 1 N, (N : ℝ) * (Λ d / (d : ℝ))
        = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, (Λ d / (d : ℝ)) := by
    rw [Finset.mul_sum]
  -- Combine with Chebyshev identity and factorial log identity.
  -- (Σ_d Λ d * ⌊N/d⌋) = Σ_n log n = log (N!).
  have hCheb : (∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ))
      = Real.log ((Nat.factorial N : ℕ) : ℝ) := by
    rw [hId N, hFL N]
  -- Set abbreviations.
  set Sd := (∑ d ∈ Finset.Icc 1 N, (Λ d / (d : ℝ))) with hSd_def
  set F := (∑ d ∈ Finset.Icc 1 N,
              Λ d * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ))) with hF_def
  -- Main identity: N * Sd = log(N!) + F.
  have hmain : (N : ℝ) * Sd = Real.log ((Nat.factorial N : ℕ) : ℝ) + F := by
    have := hsum_id
    rw [hLHS, hCheb] at this
    exact this
  -- Apply hypotheses:
  -- |log(N!) − N log N + N| ≤ C · (log N + 1).
  -- |F| ≤ C' · N.
  have hStirN : |Real.log ((Nat.factorial N : ℕ) : ℝ)
                    - (N : ℝ) * Real.log (N : ℝ) + (N : ℝ)|
                  ≤ C * (Real.log (N : ℝ) + 1) := hStirBnd N hN_ge_N₀
  have hFracN : |F| ≤ C' * (N : ℝ) := hFracBnd N
  -- Algebra: Sd − log N = (log(N!) + F)/N − log N
  --                    = (log(N!) − N log N + F)/N
  --                    = (log(N!) − N log N + N)/N + (F − N)/N.
  -- So |Sd − log N| ≤ (C·(log N + 1) + |F| + N)/N
  --               ≤ C·(log N + 1)/N + C' + 1.
  -- For N large (≥ max N₀ 1), we want to bound this by C + C' + 1.
  -- Note (log N + 1)/N ≤ 1 holds when log N + 1 ≤ N, i.e. N ≥ 1 (since log N ≤ N - 1 for N ≥ 1).
  -- Use log_le_self_of_pos? Actually Real.log N ≤ N − 1 follows from `Real.log_le_sub_one_of_pos`.
  have hlog_le_sub : Real.log (N : ℝ) ≤ (N : ℝ) - 1 := by
    -- For N ≥ 1, log N ≤ N − 1.  We use Real.add_one_le_exp / sub_one_lt or
    -- the named `Real.log_le_sub_one_of_pos`.
    exact Real.log_le_sub_one_of_pos hN_pos
  have h_log1_le_N : Real.log (N : ℝ) + 1 ≤ (N : ℝ) := by linarith
  -- From hmain, derive Sd − log N = (log(N!) − N · log N + F)/N.
  have hSd_eq : Sd - Real.log (N : ℝ)
      = (Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + F)
          / (N : ℝ) := by
    have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
    field_simp
    linarith [hmain]
  -- |Sd − log N| ≤ (|log(N!) − N log N + N| + |F − N|)/N
  --             ≤ (|log(N!) − N log N + N| + |F| + N)/N.
  -- We write the numerator as
  --   (log(N!) − N log N + N) + (F − N).
  -- Triangle.
  have hnum_split :
      Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + F
        = (Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + (N : ℝ))
            + (F - (N : ℝ)) := by ring
  have habs_num :
      |Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + F|
        ≤ |Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + (N : ℝ)|
            + |F - (N : ℝ)| := by
    rw [hnum_split]; exact abs_add_le _ _
  -- |F − N| ≤ |F| + N (since N ≥ 0).
  have habs_F_sub : |F - (N : ℝ)| ≤ |F| + (N : ℝ) := by
    have h1 : |F - (N : ℝ)| = |F + (-(N : ℝ))| := by ring_nf
    have h2 : |F + (-(N : ℝ))| ≤ |F| + |(-(N : ℝ))| := abs_add_le _ _
    have h3 : |(-(N : ℝ))| = (N : ℝ) := by
      rw [abs_neg]; exact abs_of_nonneg (by exact_mod_cast Nat.zero_le N)
    linarith [h1, h2, h3]
  -- Combine bounds on numerator.
  have habs_num' :
      |Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + F|
        ≤ C * (Real.log (N : ℝ) + 1) + C' * (N : ℝ) + (N : ℝ) := by
    calc |Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + F|
        ≤ |Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + (N : ℝ)|
            + |F - (N : ℝ)| := habs_num
      _ ≤ C * (Real.log (N : ℝ) + 1) + (|F| + (N : ℝ)) :=
          add_le_add hStirN habs_F_sub
      _ ≤ C * (Real.log (N : ℝ) + 1) + (C' * (N : ℝ) + (N : ℝ)) := by
          have : |F| ≤ C' * (N : ℝ) := hFracN
          linarith
      _ = C * (Real.log (N : ℝ) + 1) + C' * (N : ℝ) + (N : ℝ) := by ring
  -- Bound |Sd − log N| using hSd_eq.
  have habs_div : |Sd - Real.log (N : ℝ)|
      = |Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + F|
          / (N : ℝ) := by
    rw [hSd_eq]
    rw [abs_div]
    have habsN : |(N : ℝ)| = (N : ℝ) := abs_of_pos hN_pos
    rw [habsN]
  rw [habs_div]
  rw [div_le_iff₀ hN_pos]
  -- Goal: |...| ≤ (C + C' + 1) * N.
  -- From habs_num' and (log N + 1) ≤ N:
  --   |...| ≤ C * (log N + 1) + C' * N + N
  --         ≤ C * N + C' * N + N = (C + C' + 1) * N    (if C ≥ 0)
  -- But we don't know sign of C.  However: if C < 0, the bound
  -- C · (log N + 1) ≤ C · ?  ... we use that |...| ≤ ... ≤ ...
  -- The cleanest path: take Cabs := |C|, use |...| ≤ |C| · (log N + 1).
  -- But hStirBnd gives literal C; the absolute value of a bound can be ≤ C only if C ≥ 0.
  -- Since |...| ≥ 0 and ≤ C · (log N + 1) for N ≥ N₀, and log N + 1 > 0,
  -- we must have C ≥ 0 (taking any N ≥ N₀).
  -- More directly: enlarge to max(C, 0).  But here, just use that |...| ≤ C · (log N + 1)
  -- + (... ≥ 0).
  -- Strategy: split on C ≥ 0 or C < 0.  If C < 0, then C · (log N + 1) < 0,
  -- contradiction with |...| ≥ 0 except trivial.
  --
  -- Simpler: bound by (max C 0) instead.  Let's reorganize.
  have hC_lb : C * (Real.log (N : ℝ) + 1) ≥ 0 := by
    have habs_nn : (0 : ℝ) ≤ |Real.log ((Nat.factorial N : ℕ) : ℝ)
                              - (N : ℝ) * Real.log (N : ℝ) + (N : ℝ)| :=
      abs_nonneg _
    linarith [hStirN]
  have hlog1_pos : (0 : ℝ) < Real.log (N : ℝ) + 1 := by
    have hlog_nn : 0 ≤ Real.log (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_1
      exact Real.log_nonneg this
    linarith
  have hC_nn : 0 ≤ C := by
    have := hC_lb
    have := mul_nonneg_iff.mp this
    rcases this with ⟨hC, _⟩ | ⟨hC, hlog⟩
    · exact hC
    · exfalso; linarith [hlog1_pos]
  -- Now C · (log N + 1) ≤ C · N (since log N + 1 ≤ N and C ≥ 0).
  have hC_step : C * (Real.log (N : ℝ) + 1) ≤ C * (N : ℝ) := by
    exact mul_le_mul_of_nonneg_left h_log1_le_N hC_nn
  calc
    |Real.log ((Nat.factorial N : ℕ) : ℝ) - (N : ℝ) * Real.log (N : ℝ) + F|
        ≤ C * (Real.log (N : ℝ) + 1) + C' * (N : ℝ) + (N : ℝ) := habs_num'
    _ ≤ C * (N : ℝ) + C' * (N : ℝ) + (N : ℝ) := by linarith
    _ = (C + C' + 1) * (N : ℝ) := by ring

/-! ## Section 5 — Three-gap closure (with two sub-Props discharged) -/

/-- **Three-gap closure**: with `FactorialLogIdentity` and
`FractionalPartVonMangoldtBound` discharged in this file, the
`VonMangoldtSumLogN` Prop reduces to *two* remaining named gaps:

* `LogFactorialVonMangoldtIdentity` — the Chebyshev divisor-sum
  identity.
* `LogFactorialStirlingBound` — the symmetric Stirling bound.

(Closed axiom-clean.) -/
theorem vonMangoldtSumLogN_of_two_gaps
    (hId : LogFactorialVonMangoldtIdentity)
    (hStir : LogFactorialStirlingBound) :
    VonMangoldtSumLogN :=
  vonMangoldtSumLogN_of_components
    hId factorialLogIdentity_holds hStir fractionalPartVonMangoldtBound_holds

/-! ## Section 6 — End-to-end composition with P12-T1 -/

/-- **End-to-end (P12-T1 + P15-T1)**: `MertensFirstTheoremBound`
follows from the three named open Props:

```
LogFactorialVonMangoldtIdentity
  + LogFactorialStirlingBound
  + PrimePowerTailBound
    ⇒  MertensFirstTheoremBound .
```

Chain:
1. `LogFactorialVonMangoldtIdentity + LogFactorialStirlingBound ⇒
    VonMangoldtSumLogN`  (this file, via `vonMangoldtSumLogN_of_two_gaps`).
2. `VonMangoldtSumLogN + PrimePowerTailBound ⇒
    MertensFirstTheoremBound`  (P12-T1).

(Closed axiom-clean.) -/
theorem mertensFirstTheoremBound_via_vonMangoldt_components
    (hId : LogFactorialVonMangoldtIdentity)
    (hStir : LogFactorialStirlingBound)
    (hTail : PrimePowerTailBound) :
    MertensFirstTheoremBound :=
  Gdbh.PathCMertensFirstProof.mertensFirstTheoremBound_of_components
    (vonMangoldtSumLogN_of_two_gaps hId hStir) hTail

/-! ## Section 7 — Summary -/

/-- **P15-T1 summary, in proof form.**

This file decomposes the named open `VonMangoldtSumLogN` (the genuine
analytic input of Mertens 1st, classically Chebyshev–Mertens) into
four strictly smaller named open sub-Props:

1. `FactorialLogIdentity` — `Σ log n = log(N!)`.
2. `LogFactorialVonMangoldtIdentity` — `Σ Λ(d) · ⌊N/d⌋ = Σ log n`.
3. `LogFactorialStirlingBound` — symmetric Stirling.
4. `FractionalPartVonMangoldtBound` — `Σ Λ(d) · {N/d} ≤ ψ(N) = O(N)`.

Closed axiom-cleanly in this file:

* `factorialLogIdentity_holds` — sub-Prop 1.
* `fractionalPartVonMangoldtBound_holds` — sub-Prop 4 (via
  `Chebyshev.psi_le_const_mul_self` from mathlib).
* `vonMangoldtSumLogN_of_components` — the mechanical assembly bridge.
* `vonMangoldtSumLogN_of_two_gaps` — the two-gap reduction (P15-T1
  bottom line).
* `mertensFirstTheoremBound_via_vonMangoldt_components` — full P12 +
  P15 chain.

What remains open after P15-T1: the two sub-Props above.  The
**Chebyshev identity** (`LogFactorialVonMangoldtIdentity`) is a
rearrangement, provable from `vonMangoldt_sum` in mathlib via a swap
of summation order over divisor pairs.  The **Stirling bound** is the
genuine smallest analytic input now: mathlib has
`Stirling.le_log_factorial_stirling` (one half) and
`Nat.factorial_le_pow` (other half); assembling them into the
symmetric `|log(N!) − N log N + N| ≤ O(log N + 1)` is the smallest
remaining mathlib-gap.

(Closed axiom-clean.) -/
theorem pathC_p15_t1_summary : True := trivial

end PathCVonMangoldtAsymptotic
end Gdbh
