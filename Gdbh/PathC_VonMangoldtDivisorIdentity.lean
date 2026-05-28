/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P16-T1 (Phase 16 / Path C — mathlib-engineering closure of
`LogFactorialVonMangoldtIdentity`).
-/
import Gdbh.PathC_VonMangoldtAsymptotic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Path C — `LogFactorialVonMangoldtIdentity` (P16-T1)

This file is the **P16-T1 deliverable** in Phase 16.  Its target is the
named open `Prop`
`Gdbh.PathCVonMangoldtAsymptotic.LogFactorialVonMangoldtIdentity`
defined in `Gdbh/PathC_VonMangoldtAsymptotic.lean`:

```
∀ N : ℕ,
  (∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ))
    = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) .
```

We close it **unconditionally** (no `sorry`/`axiom`/`admit`) using the
mathlib v4.29.1 divisor-sum identity
`ArithmeticFunction.vonMangoldt_sum : ∑_{d ∣ n} Λ(d) = log n`.

## Strategy — classical Chebyshev sum-swap

For every `n ≥ 1`, mathlib gives the identity
`Σ_{d ∈ n.divisors} Λ(d) = log n`.  Summing this over `n ∈ Icc 1 N` and
swapping the order of summation:

```
Σ_{n ≤ N} log n  =  Σ_{n ≤ N} Σ_{d ∣ n} Λ(d)
                 =  Σ_{d ≤ N} Λ(d) · #{n ∈ Icc 1 N : d ∣ n}
                 =  Σ_{d ≤ N} Λ(d) · ⌊N/d⌋ .
```

The last equality is `Nat.Ioc_filter_dvd_card_eq_div` (mathlib v4.29.1)
plus the trivial identification `Icc 1 N = Ioc 0 N` on naturals.

## Theorem names exported

* `Gdbh.PathCVonMangoldtDivisorIdentity.icc_one_eq_ioc_zero` — `Finset.Icc 1 N = Finset.Ioc 0 N`.
* `Gdbh.PathCVonMangoldtDivisorIdentity.card_dvd_filter_eq_div` — for `d ≥ 1`,
  `#{n ∈ Icc 1 N : d ∣ n} = N / d`.
* `Gdbh.PathCVonMangoldtDivisorIdentity.divisors_eq_filter_icc` — for `n ∈ Icc 1 N`,
  `n.divisors = (Icc 1 N).filter (· ∣ n)`.
* `Gdbh.PathCVonMangoldtDivisorIdentity.logFactorialVonMangoldtIdentity_holds` —
  the closure of `LogFactorialVonMangoldtIdentity`.
-/

namespace Gdbh
namespace PathCVonMangoldtDivisorIdentity

open scoped ArithmeticFunction
open Real Finset

/-- `Finset.Icc 1 N = Finset.Ioc 0 N` on `ℕ`. -/
lemma icc_one_eq_ioc_zero (N : ℕ) :
    Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext k
  simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.lt_iff_add_one_le]

/-- For `d ≥ 1`, the number of `n ∈ Icc 1 N` divisible by `d` equals
`N / d`.  This is the integer-multiple counting formula. -/
lemma card_dvd_filter_eq_div (N d : ℕ) :
    (((Finset.Icc 1 N).filter (fun n => d ∣ n)).card : ℕ) = N / d := by
  rw [icc_one_eq_ioc_zero]
  -- Mathlib: `Nat.Ioc_filter_dvd_card_eq_div : #{x ∈ Ioc 0 N | d ∣ x} = N / d`
  exact Nat.Ioc_filter_dvd_card_eq_div N d

/-- For `n ∈ Icc 1 N` (so `1 ≤ n ≤ N`), the divisor finset coincides with
filtering `Icc 1 N` by divisibility by `n`. -/
lemma divisors_eq_filter_icc {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    n.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ n) := by
  rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
  have hn_ne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  ext d
  constructor
  · intro hd
    have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd_le : d ≤ n := Nat.divisor_le hd
    refine Finset.mem_filter.mpr ⟨?_, hd_dvd⟩
    exact Finset.mem_Icc.mpr ⟨hd_pos, hd_le.trans hnN⟩
  · intro hd
    rcases Finset.mem_filter.mp hd with ⟨_, hd_dvd⟩
    exact Nat.mem_divisors.mpr ⟨hd_dvd, hn_ne⟩

/-- **Closure** of `LogFactorialVonMangoldtIdentity`.

For every `N : ℕ`,

```
Σ_{d ∈ Icc 1 N} Λ(d) · (N / d) = Σ_{n ∈ Icc 1 N} log n .
```

Proof: expand `log n = Σ_{d ∈ n.divisors} Λ(d)` (mathlib's
`ArithmeticFunction.vonMangoldt_sum`), rewrite the divisor finset as
`(Icc 1 N).filter (· ∣ n)` (since `1 ≤ n ≤ N` makes every divisor lie in
`Icc 1 N`), swap the order of summation via `Finset.sum_comm`, and
identify the inner count `#{n ∈ Icc 1 N : d ∣ n} = N / d`
(`Nat.Ioc_filter_dvd_card_eq_div`). -/
theorem logFactorialVonMangoldtIdentity_holds :
    Gdbh.PathCVonMangoldtAsymptotic.LogFactorialVonMangoldtIdentity := by
  classical
  intro N
  -- Right-hand side: rewrite each `log n` via `vonMangoldt_sum`, then
  -- replace `n.divisors` with `(Icc 1 N).filter (· ∣ n)`.
  have hRHS :
      (∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ))
        = ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ n),
              ArithmeticFunction.vonMangoldt d := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    -- log n = Σ_{d ∈ n.divisors} Λ d
    have hsum : (∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d)
        = Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_sum
    -- and `n.divisors = filter (· ∣ n) (Icc 1 N)` for `n ∈ Icc 1 N`.
    have hdivs : n.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ n) :=
      divisors_eq_filter_icc hn
    rw [← hsum, hdivs]
  -- Now swap the order of summation on the (filtered) double sum.
  -- Push the filter into the sum-body as an `if`:
  --   Σ_n Σ_{d ∈ Icc 1 N | d ∣ n} Λ d = Σ_n Σ_{d ∈ Icc 1 N} (if d ∣ n then Λ d else 0).
  have hSwap :
      (∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ n),
            ArithmeticFunction.vonMangoldt d)
        = ∑ d ∈ Finset.Icc 1 N,
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
              ArithmeticFunction.vonMangoldt d := by
    -- Both sides equal Σ_n Σ_d (if d ∣ n then Λ d else 0) and vice versa.
    have hL :
        (∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ n),
              ArithmeticFunction.vonMangoldt d)
          = ∑ n ∈ Finset.Icc 1 N,
              ∑ d ∈ Finset.Icc 1 N,
                if d ∣ n then ArithmeticFunction.vonMangoldt d else 0 := by
      refine Finset.sum_congr rfl ?_
      intro n _
      exact Finset.sum_filter _ _
    have hR :
        (∑ d ∈ Finset.Icc 1 N,
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
              ArithmeticFunction.vonMangoldt d)
          = ∑ d ∈ Finset.Icc 1 N,
              ∑ n ∈ Finset.Icc 1 N,
                if d ∣ n then ArithmeticFunction.vonMangoldt d else 0 := by
      refine Finset.sum_congr rfl ?_
      intro d _
      exact Finset.sum_filter _ _
    rw [hL, hR, Finset.sum_comm]
  -- Inner sum simplifies to Λ d · (N / d).
  have hCard :
      (∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
            ArithmeticFunction.vonMangoldt d)
        = ∑ d ∈ Finset.Icc 1 N,
            ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro d _
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    exact_mod_cast card_dvd_filter_eq_div N d
  -- Assemble:
  --   Σ_n log n  =  Σ_n Σ_{d ∈ filter} Λ d  (hRHS)
  --              =  Σ_d Σ_{n ∈ filter} Λ d  (hSwap)
  --              =  Σ_d Λ d · (N / d)        (hCard)
  -- The goal is `(∑ d, Λ d · (N/d)) = ∑ n, log n`, i.e. the reverse.
  -- We chain the equalities and apply `.symm`.
  calc (∑ d ∈ Finset.Icc 1 N,
            ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ))
        = ∑ d ∈ Finset.Icc 1 N,
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
              ArithmeticFunction.vonMangoldt d := hCard.symm
    _ = ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ n),
              ArithmeticFunction.vonMangoldt d := hSwap.symm
    _ = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := hRHS.symm

end PathCVonMangoldtDivisorIdentity
end Gdbh
