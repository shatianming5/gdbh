import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Path A — Vaughan's combinatorial identity for the von Mangoldt function

This file is the **purely combinatorial** core of the Vinogradov–Vaughan
minor arc bound: the algebraic identity

```
Λ = μ_{≤U} ∗ log + μ_{>U} ∗ Λ_{≤U} ∗ ζ + μ_{>U} ∗ Λ_{>U} ∗ ζ
```

in the ring `ArithmeticFunction ℝ` of arithmetic functions under
Dirichlet convolution.  The three summands correspond, after summation
against an additive character `e(mα)`, to the three classical sums in
the Vinogradov–Vaughan argument:

* **Type I** `S_I = ∑_n (μ_{≤U} ∗ log)(n) · e(nα)`: a "linear" sum, of
  the form `∑_{d ≤ U} μ(d) ∑_{m} log m · e(dmα)`.  Handled via
  summation by parts on the inner geometric sum.
* **Type II** `S_II = ∑_n (μ_{>U} ∗ Λ_{≤U} ∗ ζ)(n) · e(nα)`: a bilinear
  sum, of the form `∑_{d > U} μ(d) ∑_{k ≤ U} Λ(k) ∑_{m} e(dkmα)`.
  Handled by Cauchy–Schwarz.
* **Type III** `S_III = ∑_n (μ_{>U} ∗ Λ_{>U} ∗ ζ)(n) · e(nα)`: the
  "high–high" piece, also a bilinear sum, handled in the same way.

The analytic estimates on the sums `S_I`, `S_II`, `S_III` are not part
of this file (they are recorded in `Gdbh/PathA_MinorArc.lean`); this
file proves only the algebraic identity that produces the
decomposition, together with the corresponding decomposition of the
trigonometric sum.

## Main results (all axiom-clean)

* `ArithmeticFunction.truncLE`, `truncGT` — truncation operators.
* `truncLE_add_truncGT` — every function is the sum of its low/high
  parts: `f = truncLE f U + truncGT f U`.
* `vaughan_identity` — Vaughan's identity at the function level.
* `vaughan_sum_decomposition` — the corresponding decomposition of any
  weighted sum `∑_n Λ(n) · w(n)`.
* `vaughan_cosine_sum_decomposition` — the typed decomposition for the
  trigonometric sum `∑_n Λ(n) · cos(2π m α)` that feeds directly into
  `PathAMinorArc.VaughanDecomposition`.

## Mathematical content vs. analytic content

The Vaughan identity is a **purely algebraic** statement in the ring of
arithmetic functions; it follows directly from
`Λ = μ ∗ log` and `Λ ∗ ζ = log` (both in mathlib) together with the
elementary distributive identity `μ = μ_{≤U} + μ_{>U}` (and similarly
for `Λ`).  All bilinear/Cauchy–Schwarz/summation-by-parts work goes
into bounding the resulting sums; that is **not** part of this file.
-/

namespace Gdbh
namespace PathAVaughan

open Real Filter BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## Section 1 — Truncation operators on arithmetic functions

Given an arithmetic function `f : ArithmeticFunction ℝ` and a threshold
`U : ℕ`, we define
`truncLE f U n = f n` if `n ≤ U`, else `0`, and
`truncGT f U n = f n` if `n > U`, else `0`.

These are themselves arithmetic functions (i.e. they send `0 ↦ 0`,
which holds for free because `f 0 = 0`).  The basic invariants are
`f = truncLE f U + truncGT f U` and the obvious case-analysis
characterizations. -/

/-- `truncLE f U` keeps the values of `f` on `n ≤ U` and zeroes the rest. -/
noncomputable def truncLE (f : ArithmeticFunction ℝ) (U : ℕ) :
    ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by
    by_cases hU : 0 ≤ U
    · simp
    · simp at hU⟩

/-- `truncGT f U` keeps the values of `f` on `n > U` and zeroes the rest. -/
noncomputable def truncGT (f : ArithmeticFunction ℝ) (U : ℕ) :
    ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] lemma truncLE_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    truncLE f U n = if n ≤ U then f n else 0 := rfl

@[simp] lemma truncGT_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    truncGT f U n = if U < n then f n else 0 := rfl

/-- The fundamental decomposition: every arithmetic function is the sum
of its low and high parts. -/
theorem truncLE_add_truncGT (f : ArithmeticFunction ℝ) (U : ℕ) :
    truncLE f U + truncGT f U = f := by
  ext n
  simp only [add_apply, truncLE_apply, truncGT_apply]
  by_cases hn : n ≤ U
  · simp [hn, Nat.not_lt.mpr hn]
  · have hn' : U < n := Nat.lt_of_not_ge hn
    simp [hn, hn']

/-- Reordered form of `truncLE_add_truncGT`. -/
theorem truncGT_add_truncLE (f : ArithmeticFunction ℝ) (U : ℕ) :
    truncGT f U + truncLE f U = f := by
  rw [add_comm, truncLE_add_truncGT]

/-! ## Section 2 — Vaughan's identity at the function level

We work in the commutative semiring `ArithmeticFunction ℝ`.  The
identity

```
Λ = μ_{≤U} ∗ log + μ_{>U} ∗ Λ_{≤U} ∗ ζ + μ_{>U} ∗ Λ_{>U} ∗ ζ
```

follows from three mathlib facts and ring manipulation:

1. `μ ∗ log = Λ` (`moebius_mul_log_eq_vonMangoldt`),
2. `Λ ∗ ζ = log` (`vonMangoldt_mul_zeta`),
3. `(truncLE g U) + (truncGT g U) = g` (above).

Step (1) gives the starting point, step (3) splits `μ` and `Λ` into
truncated pieces, and step (2) rewrites the high–μ piece using
`log = Λ ∗ ζ`. -/

/-- A convenient real-valued name for the Möbius function. -/
noncomputable abbrev μℝ : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

/-- A convenient real-valued name for the ζ function. -/
noncomputable abbrev ζℝ : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

/-- Restatement of `moebius_mul_log_eq_vonMangoldt` in our local name. -/
theorem μℝ_mul_log :
    μℝ * ArithmeticFunction.log = ArithmeticFunction.vonMangoldt :=
  ArithmeticFunction.moebius_mul_log_eq_vonMangoldt

/-- Restatement of `vonMangoldt_mul_zeta` in our local names. -/
theorem vonMangoldt_mul_ζℝ :
    ArithmeticFunction.vonMangoldt * ζℝ = ArithmeticFunction.log :=
  ArithmeticFunction.vonMangoldt_mul_zeta

/-- **Vaughan's identity** (function-level form).

For every `U : ℕ`, in the ring `ArithmeticFunction ℝ` we have
```
Λ = μ_{≤U} ∗ log + μ_{>U} ∗ Λ_{≤U} ∗ ζ + μ_{>U} ∗ Λ_{>U} ∗ ζ.
```

The proof is pure ring manipulation, using
`Λ = μ ∗ log`, `Λ ∗ ζ = log`, and the splitting
`g = g_{≤U} + g_{>U}` for `g ∈ {μ, Λ}`. -/
theorem vaughan_identity (U : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      truncLE μℝ U * ArithmeticFunction.log
      + truncGT μℝ U * truncLE ArithmeticFunction.vonMangoldt U * ζℝ
      + truncGT μℝ U * truncGT ArithmeticFunction.vonMangoldt U * ζℝ := by
  -- Step A: Λ = (μ_{≤U} + μ_{>U}) * log.
  have hSplitμ : μℝ = truncLE μℝ U + truncGT μℝ U :=
    (truncLE_add_truncGT μℝ U).symm
  have hSplitΛ :
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
        truncLE ArithmeticFunction.vonMangoldt U
          + truncGT ArithmeticFunction.vonMangoldt U :=
    (truncLE_add_truncGT ArithmeticFunction.vonMangoldt U).symm
  -- Λ = μ * log
  have hΛ : (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      μℝ * ArithmeticFunction.log := by
    rw [μℝ_mul_log]
  -- Substitute μ = μ_{≤U} + μ_{>U}.
  have hExpand1 :
      μℝ * ArithmeticFunction.log =
        truncLE μℝ U * ArithmeticFunction.log
        + truncGT μℝ U * ArithmeticFunction.log := by
    conv_lhs => rw [hSplitμ]
    ring
  -- For the high-μ piece, replace log by Λ * ζ.
  have hExpand2 :
      truncGT μℝ U * ArithmeticFunction.log =
        truncGT μℝ U *
          (ArithmeticFunction.vonMangoldt * ζℝ) := by
    rw [vonMangoldt_mul_ζℝ]
  -- Substitute Λ = Λ_{≤U} + Λ_{>U}.
  have hExpand3 :
      truncGT μℝ U *
        ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) * ζℝ) =
      truncGT μℝ U * truncLE ArithmeticFunction.vonMangoldt U * ζℝ
        + truncGT μℝ U * truncGT ArithmeticFunction.vonMangoldt U * ζℝ := by
    conv_lhs => rw [hSplitΛ]
    ring
  -- Assemble.
  calc (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ)
      = μℝ * ArithmeticFunction.log := hΛ
    _ = truncLE μℝ U * ArithmeticFunction.log
        + truncGT μℝ U * ArithmeticFunction.log := hExpand1
    _ = truncLE μℝ U * ArithmeticFunction.log
        + truncGT μℝ U *
            ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) * ζℝ) := by
        rw [hExpand2]
    _ = truncLE μℝ U * ArithmeticFunction.log
        + (truncGT μℝ U * truncLE ArithmeticFunction.vonMangoldt U * ζℝ
           + truncGT μℝ U * truncGT ArithmeticFunction.vonMangoldt U * ζℝ) := by
        rw [hExpand3]
    _ = truncLE μℝ U * ArithmeticFunction.log
        + truncGT μℝ U * truncLE ArithmeticFunction.vonMangoldt U * ζℝ
        + truncGT μℝ U * truncGT ArithmeticFunction.vonMangoldt U * ζℝ := by
        ring

/-- **Pointwise Vaughan identity.**  For every natural number `n` and
every truncation parameter `U`, the identity holds pointwise. -/
theorem vaughan_identity_apply (U n : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n =
      (truncLE μℝ U * ArithmeticFunction.log) n
      + (truncGT μℝ U * truncLE ArithmeticFunction.vonMangoldt U * ζℝ) n
      + (truncGT μℝ U * truncGT ArithmeticFunction.vonMangoldt U * ζℝ) n := by
  have h := vaughan_identity U
  have hap := congrArg (fun g : ArithmeticFunction ℝ => g n) h
  simpa using hap

/-! ## Section 3 — Decomposition of weighted exponential-type sums

Given the function-level identity, summing both sides against any
weight `w : ℕ → ℝ` yields a decomposition of `∑ Λ(n) · w(n)` into three
pieces.  In particular, for the additive-character weight
`w(n) = cos(2π · n · α)` (the real part of `e(nα)`), this is exactly
the input needed by `PathAMinorArc.VaughanDecomposition`. -/

/-- **Vaughan sum decomposition** for an arbitrary weight `w`. -/
theorem vaughan_sum_decomposition (U : ℕ) (s : Finset ℕ) (w : ℕ → ℝ) :
    ∑ n ∈ s,
        ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n) * w n =
      (∑ n ∈ s, (truncLE μℝ U * ArithmeticFunction.log) n * w n)
      + (∑ n ∈ s,
          (truncGT μℝ U * truncLE ArithmeticFunction.vonMangoldt U * ζℝ) n
          * w n)
      + (∑ n ∈ s,
          (truncGT μℝ U * truncGT ArithmeticFunction.vonMangoldt U * ζℝ) n
          * w n) := by
  have hpt : ∀ n,
      ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n) * w n =
        (truncLE μℝ U * ArithmeticFunction.log) n * w n
        + (truncGT μℝ U * truncLE ArithmeticFunction.vonMangoldt U * ζℝ) n
            * w n
        + (truncGT μℝ U * truncGT ArithmeticFunction.vonMangoldt U * ζℝ) n
            * w n := by
    intro n
    have := vaughan_identity_apply U n
    rw [this]
    ring
  calc ∑ n ∈ s,
      ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n) * w n
      = ∑ n ∈ s,
          ((truncLE μℝ U * ArithmeticFunction.log) n * w n
           + (truncGT μℝ U * truncLE ArithmeticFunction.vonMangoldt U * ζℝ) n
              * w n
           + (truncGT μℝ U * truncGT ArithmeticFunction.vonMangoldt U * ζℝ) n
              * w n) := by
        refine Finset.sum_congr rfl ?_
        intro n _
        exact hpt n
    _ = (∑ n ∈ s, (truncLE μℝ U * ArithmeticFunction.log) n * w n)
        + (∑ n ∈ s,
            (truncGT μℝ U * truncLE ArithmeticFunction.vonMangoldt U * ζℝ) n
              * w n)
        + (∑ n ∈ s,
            (truncGT μℝ U * truncGT ArithmeticFunction.vonMangoldt U * ζℝ) n
              * w n) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-! ## Section 4 — Typed Vaughan decomposition for the cosine sum

The form needed by `Gdbh.PathAMinorArc.VaughanDecomposition` packages
the three pieces as three real numbers whose sum is the trigonometric
sum.  We extract them from the general decomposition above. -/

/-- The Type I sum from Vaughan's identity (function-level form). -/
noncomputable def TypeI_sum (U N : ℕ) (α : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
      (truncLE μℝ U * ArithmeticFunction.log) n
        * Real.cos (2 * Real.pi * n * α)

/-- The Type II sum from Vaughan's identity (function-level form). -/
noncomputable def TypeII_sum (U N : ℕ) (α : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
      (truncGT μℝ U * truncLE ArithmeticFunction.vonMangoldt U * ζℝ) n
        * Real.cos (2 * Real.pi * n * α)

/-- The Type III ("high–high") sum from Vaughan's identity. -/
noncomputable def TypeIII_sum (U N : ℕ) (α : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
      (truncGT μℝ U * truncGT ArithmeticFunction.vonMangoldt U * ζℝ) n
        * Real.cos (2 * Real.pi * n * α)

/-- **Vaughan decomposition for the cosine sum**: for every `U, N, α`,
the trigonometric sum `∑_{n ≤ N} Λ(n) cos(2π n α)` decomposes as
`TypeI + TypeII + TypeIII`. -/
theorem vaughan_cosine_sum_decomposition (U N : ℕ) (α : ℝ) :
    ∑ n ∈ Finset.range (N + 1),
        ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n)
          * Real.cos (2 * Real.pi * n * α) =
      TypeI_sum U N α + TypeII_sum U N α + TypeIII_sum U N α := by
  -- This is just `vaughan_sum_decomposition` with
  -- `s = range (N+1)` and `w n = cos (2π n α)`.
  simpa [TypeI_sum, TypeII_sum, TypeIII_sum] using
    vaughan_sum_decomposition U (Finset.range (N + 1))
      (fun n => Real.cos (2 * Real.pi * (n : ℝ) * α))

end PathAVaughan
end Gdbh
