/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T17 (Selberg sieve route exploration)
-/
import Mathlib.NumberTheory.SelbergSieve
import Gdbh.PathC_PairedBrunGoldbachAtSqrt
import Gdbh.PathC_PairedBonferroniNaturalSubSqrt

/-!
# Path C — P19-T17: Selberg sieve as alternative to Brun-Bonferroni

## Mission

P19-T14 and P19-T16 attack the genuine Brun-Bonferroni inequality at
truncation depth `k = 2n` for closing two residuals:

* `AlignedInequalityAndTail`
  (`Gdbh/PathC_PairedBrunGoldbachAtSqrt.lean`, l. 485)
* `PairedBonferroniNaturalSubSqrtCombinatorialKernel`
  (`Gdbh/PathC_PairedBonferroniNaturalSubSqrt.lean`, l. 147)

This file explores whether mathlib v4.29.1's `Mathlib.NumberTheory.SelbergSieve`
framework can substitute for the manual Brun-Bonferroni argument by giving
an equivalent or stronger upper bound via the Λ² majorant.

## What mathlib provides

Reading `Mathlib.NumberTheory.SelbergSieve` (a single 227-line file
authored by Arend Mellendijk, after Heath-Brown's "Lectures on sieves"):

The mathlib file exposes a **single-sift** framework:

* `BoundingSieve` (structure):  packages a finite weighted set
  `support : Finset ℕ` with weights `weights : ℕ → ℝ`, a squarefree
  product of primes `prodPrimes : ℕ` whose multiples are sifted, an
  approximate total mass `totalMass : ℝ`, and a multiplicative density
  function `nu : ArithmeticFunction ℝ` with `0 < ν(p) < 1` for primes
  `p ∣ prodPrimes`.

* `SelbergSieve` extends `BoundingSieve` with a real `level : ℝ`
  (the truncation parameter `y = √D` in Selberg's argument).

* `BoundingSieve.multSum d`:  `∑ n ∈ support, [d ∣ n] * weights n`,
  the (weighted) count of multiples of `d`.

* `BoundingSieve.rem d := multSum d - nu d * totalMass`:  the residual
  in the approximation `multSum d ≈ nu d · totalMass`.

* `BoundingSieve.siftedSum`:  `∑ n ∈ support, [Coprime prodPrimes n] *
  weights n`, the post-sift mass.

* `BoundingSieve.mainSum muPlus := ∑ d ∈ divisors prodPrimes, muPlus d *
  nu d`.

* `BoundingSieve.errSum muPlus := ∑ d ∈ divisors prodPrimes, |muPlus d|
  * |rem d|`.

* `BoundingSieve.IsUpperMoebius muPlus`:  the abstract "upper Möbius"
  side condition `∀ n, [n=1] ≤ ∑_{d∣n} muPlus(d)`, satisfied by both the
  truncated-Möbius (Brun) and Λ²-majorant (Selberg) choices.

* `BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius` (the only
  delivery theorem):  for any `muPlus` satisfying `IsUpperMoebius`,
  `siftedSum ≤ totalMass * mainSum muPlus + errSum muPlus`.

**What mathlib does *not* yet provide**:

1. No Λ² weights are constructed.  The file mentions diagonalisation
   of the main term but does not deliver the concrete Selberg optimum
   `λ_d = (μ(d)/g(d)) · ∑_{m ≤ z/d, gcd(m,d)=1} 1/g(m) / ∑_{m ≤ z} 1/g(m)`.

2. No paired sift.  The framework is by design a single-sift: the
   `support`, `prodPrimes`, `nu` schema sifts a *one-dimensional*
   weighted set by *one* prime ideal.  The Goldbach paired sift
   `{m(n - m) : 1 ≤ m < n}` requires the *two-dimensional* extension
   `nu(d) = (number of pairs (a,b) mod d : a + b ≡ n, gcd(ab,d) = 1)/d`,
   which is the Bombieri-style "Selberg over a doubly-multiplicative
   density" not in mathlib.

3. No Mertens product estimate `∏_{p ≤ z}(1 - ν(p)) ≪ 1/(log z)^κ`,
   no fundamental lemma `M(z) ≤ Cκ/(log z)^κ`.

Consequently: **mathlib v4.29.1's Selberg sieve cannot directly close
`AlignedInequalityAndTail` or
`PairedBonferroniNaturalSubSqrtCombinatorialKernel`.**  It provides
*one* abstract delivery theorem
(`siftedSum_le_mainSum_errSum_of_upperMoebius`) that decomposes any
upper-Möbius weight into (main term) + (error term), but the heavy
lifting of constructing those weights and bounding the resulting sums
for the *paired* Goldbach sift is exactly the Halberstam-Richert §3 /
Bombieri material that has not yet been formalised.

This file:

1. Documents the mathlib framework precisely.

2. Defines a `SelbergRoute` paired analogue Prop
   `SelbergPairedGoldbachBound` of the same shape as
   `AlignedInequalityAndTail` minus the alignment constraint with the
   T5-Sqrt tail, encoding the bound the Selberg approach is *expected*
   to provide were paired-sift Selberg formalised.

3. Records the **gap analysis**:  what missing mathlib pieces would
   need to be added to make Selberg substitute for Brun-Bonferroni in
   our setting.

4. Exposes the **honest conclusion**:  the manual paired Brun-Bonferroni
   route from P19-T14 / P19-T16 is necessary in mathlib v4.29.1.

All theorems are axiom-clean: only `propext`, `Classical.choice`,
`Quot.sound`.

## References

* A. Selberg, *On an elementary method in the theory of primes*,
  Norske Vid. Selsk. Forh. Trondheim 19 (1947), 64-67.
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  §§ 3-4 (Selberg's Λ² sieve).
* D. R. Heath-Brown, *Lectures on sieves*, 2002.
* A. Mellendijk, `Mathlib.NumberTheory.SelbergSieve`, 2024.
-/

namespace Gdbh
namespace PathCSelbergRoute

open Finset Real
open Gdbh.PathCBrunSieve
open Gdbh.PathCGoldbachRBound
open Gdbh.PathCMertensProof (pairedBrunFactor)
open Gdbh.PathCPairedBrunGoldbachAtSqrt (AlignedInequalityAndTail)
open Gdbh.PathCPairedBonferroniNaturalSubSqrt
  (PairedBonferroniNaturalSubSqrtCombinatorialKernel)

/-! ## Section 1 — What `Mathlib.NumberTheory.SelbergSieve` provides

These re-exports are *type aliases* over the mathlib structures, kept
here so the file is self-contained: a reader can see at a glance what
the upstream Selberg framework offers without leaving this module. -/

/-- Re-export: the mathlib `BoundingSieve` data structure.  This is the
abstract sieve set-up — a weighted finite set together with a squarefree
product of sieving primes and a multiplicative density `ν`. -/
abbrev MathlibBoundingSieve := BoundingSieve

/-- Re-export: the mathlib `SelbergSieve` data structure.  Extends
`BoundingSieve` with a level parameter `y ≥ 1` (the Selberg `y = √D`). -/
abbrev MathlibSelbergSieve := SelbergSieve

/-- Re-export: the mathlib `IsUpperMoebius` predicate.  A weight system
`muPlus : ℕ → ℝ` is upper-Möbius if `∀ n, [n = 1] ≤ ∑_{d ∣ n} muPlus(d)`.
Both Brun's truncated Möbius and Selberg's Λ² majorant satisfy this. -/
abbrev IsUpperMoebius := @BoundingSieve.IsUpperMoebius

/-- **The single delivery theorem mathlib provides for Selberg.**

For any `BoundingSieve s` and any upper-Möbius weight `muPlus`,
`siftedSum ≤ totalMass · mainSum(muPlus) + errSum(muPlus)`.

This is purely the abstract decomposition; mathlib does *not* construct
the optimal Selberg `muPlus = Λ²` or bound the resulting `mainSum` /
`errSum`. -/
theorem mathlib_selberg_delivers
    (s : BoundingSieve) (muPlus : ℕ → ℝ) (h : IsUpperMoebius muPlus) :
    s.siftedSum ≤ s.totalMass * s.mainSum muPlus + s.errSum muPlus :=
  BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius muPlus h

/-! ## Section 2 — Why mathlib's single-sift Selberg cannot directly
close the paired Goldbach residuals

The `Gdbh` paired sift `goldbachSiftedPair n z` counts `m ∈ [1, n - 1]`
such that *both* `m` and `n - m` have no prime factor `≤ z`.  This is a
**two-dimensional** sift over the pair `(m, n - m)`.

To shoehorn this into mathlib's single-sift `BoundingSieve` framework,
one would set
```
support  = Finset.Icc 1 (n - 1),
weights  = fun m ↦ [(n - m) coprime to z#],
totalMass ≈ n · (paired local factor at z),
nu d     = (number of m mod d : both m and n - m coprime to d) / d
         = (singular series local factor at d),
prodPrimes = primorial z.
```

This *does* fit the mathlib schema in principle.  But:

(i) `weights` is then itself a sieve-like indicator (depending on `z`),
not a fixed weight as the framework assumes.  Mathlib's framework
permits arbitrary `weights ≥ 0`, so the typing goes through, but the
factorisation of the resulting `siftedSum` no longer matches the
classical bound shape.

(ii) The density `nu d = ω(d) / d`, where `ω(d)` is the number of
"forbidden" residues mod `d`.  For the paired Goldbach sift, `ω(p) = 2`
for odd primes `p ∤ n` and `ω(p) = 1` for primes `p ∣ n`, `p` odd
(Goldbach's local-factor distinction).  Mathlib *does* accommodate this
via the `nu` field — but only as a hypothesis, not by constructing it.

(iii) Even with the structure populated, mathlib does not deliver the
**Λ² weights** or the **main-term bound** `mainSum(Λ²) ≤ 1 / V(z)`
where `V(z) = ∑_{d ≤ z, d squarefree} g(d)` with `g(d) = ∏_{p ∣ d}
ν(p)/(1 - ν(p))`.  This is the analytic heart of Selberg's argument
and is absent from `Mathlib.NumberTheory.SelbergSieve`.

(iv) Finally, mathlib does not provide a Mertens-style estimate
`1/V(z) ≪ 1/(log z)^2` for the paired density `ν(p) = 2/p`.

Conclusion:  **mathlib's `SelbergSieve` is a Prop-level framework
without the analytic content**.  In our terminology, it is the
*assembly skeleton* of Selberg, analogous to our `Gdbh.PathCBrunSieve`
file's `BrunMainTerm` + `BrunErrorTerm` + `MertensProductBound`
decomposition, but with `mainSum + errSum` instead of `BrunMainTerm +
BrunErrorTerm`.  The genuine analytic residuals are the same: the
Mertens product bound and the truncation-error bound. -/

/-! ## Section 3 — The Selberg-shape paired Goldbach Prop

We *define* the Prop that mathlib's Selberg sieve would deliver were
the paired-sift extension and Mertens estimates available.  This is
the Selberg analogue of `AlignedInequalityAndTail` (without the
tail-alignment clause). -/

/-- **The Selberg-shape paired Goldbach bound.**

The Λ² Selberg majorant for the paired Goldbach sift, were it
constructed in mathlib, would deliver an inequality of the form
```
goldbachSiftedPair n z  ≤  C₁ · n · M(z)
                        +  C₁ · n · ω(z)^(2k+1)/(2k+1)!,
```
where `M(z)` is the Selberg main-term factor (analogous to
`pairedBrunFactor z` for the truncated-Möbius / Brun route) and the
second summand is the Selberg-Λ² error term (analogous to the
Brun-Bonferroni tail).

This Prop, applied at `z = √n`, has *exactly* the shape of the
inequality part of `AlignedInequalityAndTail`, with the Selberg main-
term factor `M` substituted for `pairedBrunFactor`. -/
def SelbergPairedGoldbachBound (M : ℕ → ℝ) : Prop :=
  ∃ C₁ : ℝ, ∃ N : ℕ, ∃ k : ℕ → ℕ,
    0 < C₁ ∧ 4 ≤ N ∧
    (∀ n : ℕ, N ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * M (Nat.sqrt n)
          + C₁ * (n : ℝ)
              * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
              / ((2 * k n + 1).factorial : ℝ))

/-- **The Selberg-to-Brun factor equivalence (upper direction).**

Halberstam-Richert §4 Theorem 3: for the paired Goldbach density
`ν(p) = 2/p` (odd primes), the Selberg main-term factor `M(z) = 1/V(z)`
and the Brun factor `pairedBrunFactor(z) = ∏_{p ≤ z, odd}(1 - 2/p)`
satisfy `M(z) ≤ C · pairedBrunFactor(z)` for some absolute `C > 0`.

We expose this as a Prop because mathlib v4.29.1 does not provide it
either: it is part of the same body of classical sieve analysis that
mathlib's `SelbergSieve` file lacks. -/
def MathlibBrunSelbergFactorEquivalence (M : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, M z ≤ C * pairedBrunFactor z

/-! ## Section 4 — The bridge: Selberg + reverse equivalence ⇒
Brun-factor-shape bound

If mathlib *were* to deliver `SelbergPairedGoldbachBound M` for some
concrete `M` (the Selberg main-term factor for the paired Goldbach
density), and if we have `MathlibBrunSelbergFactorEquivalence M`,
then we can extract a bound of the same shape as the *inequality*
clause of `AlignedInequalityAndTail`, with constants scaled by `C`.

This bridge is **mechanical** and we prove it axiom-clean. -/

/-- **Bridge:**  Selberg bound + reverse equivalence (`M ≤ C ·
pairedBrunFactor`) ⇒ Brun-factor-shape inequality.

The proof uses that the error term's leading coefficient `C₁` is the
same on both sides, but we *uniformly inflate* both the main-term and
error-term coefficients to `C₁ · (1 + C)`, which dominates `C₁ · C` for
the main term (via `M ≤ C · pairedBrunFactor`) and `C₁` for the error
term (via `1 ≤ 1 + C`).  This avoids any assumption about whether
`C ≥ 1` or `C < 1`. -/
theorem brunFactor_shape_inequality_of_selberg
    (M : ℕ → ℝ)
    (hSelberg : SelbergPairedGoldbachBound M)
    (hRev     : MathlibBrunSelbergFactorEquivalence M) :
    ∃ C₂ : ℝ, ∃ N : ℕ, ∃ k : ℕ → ℕ,
      0 < C₂ ∧ 4 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C₂ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + C₂ * (n : ℝ)
                * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ) := by
  classical
  obtain ⟨C₁, N, k, hC₁, hN, hbound⟩ := hSelberg
  obtain ⟨C, hC, hMle⟩ := hRev
  -- Choose C₂ = C₁ · (1 + C).  This dominates C₁ (giving an upper
  -- bound on the error coefficient, since C > 0 gives 1 + C > 1) and
  -- C₁ · C (giving an upper bound on the main-term coefficient).
  refine ⟨C₁ * (1 + C), N, k, ?_, hN, ?_⟩
  · have h1C_pos : 0 < 1 + C := by linarith
    exact mul_pos hC₁ h1C_pos
  intro n hn
  have hgoldsift_le := hbound n hn
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have hC₁_nn : (0 : ℝ) ≤ C₁ := le_of_lt hC₁
  have hC₁n_nn : (0 : ℝ) ≤ C₁ * (n : ℝ) := mul_nonneg hC₁_nn hn_nn
  have hC_nn : (0 : ℝ) ≤ C := le_of_lt hC
  have hPBnn : 0 ≤ pairedBrunFactor (Nat.sqrt n) := by
    have := Gdbh.PathCMertensProof.pairedBrunFactor_pos (Nat.sqrt n)
    linarith
  -- Main term bound.
  -- C₁ · n · M(√n) ≤ C₁ · n · (C · pairedBrunFactor(√n))
  --              = (C₁ · C) · n · pairedBrunFactor(√n)
  --              ≤ (C₁ · (1+C)) · n · pairedBrunFactor(√n)
  --   (using C₁ · C ≤ C₁ · (1+C), i.e. C ≤ 1 + C, true).
  have hMle_z := hMle (Nat.sqrt n)
  have hMain_step1 :
      C₁ * (n : ℝ) * M (Nat.sqrt n)
        ≤ C₁ * (n : ℝ) * (C * pairedBrunFactor (Nat.sqrt n)) :=
    mul_le_mul_of_nonneg_left hMle_z hC₁n_nn
  have hC_le_1pC : C ≤ 1 + C := by linarith
  -- (C₁ · n) · (C · pBF) ≤ (C₁ · n) · ((1 + C) · pBF)  since pBF ≥ 0.
  have hMain_step2 :
      C₁ * (n : ℝ) * (C * pairedBrunFactor (Nat.sqrt n))
        ≤ C₁ * (n : ℝ) * ((1 + C) * pairedBrunFactor (Nat.sqrt n)) := by
    apply mul_le_mul_of_nonneg_left _ hC₁n_nn
    exact mul_le_mul_of_nonneg_right hC_le_1pC hPBnn
  have hMain_eq :
      C₁ * (n : ℝ) * ((1 + C) * pairedBrunFactor (Nat.sqrt n))
        = C₁ * (1 + C) * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by ring
  have hMain :
      C₁ * (n : ℝ) * M (Nat.sqrt n)
        ≤ C₁ * (1 + C) * (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
    have := hMain_step1.trans hMain_step2
    rw [hMain_eq] at this
    exact this
  -- Error term bound.
  -- C₁ · n · (π(√n))^(2k+1) / (2k+1)!
  --   ≤ (C₁ · (1+C)) · n · (π(√n))^(2k+1) / (2k+1)!
  -- using C₁ ≤ C₁ · (1+C) (since 1 ≤ 1+C and C₁ > 0).
  have hC₁_le : C₁ ≤ C₁ * (1 + C) := by
    have h1_le_1pC : (1 : ℝ) ≤ 1 + C := by linarith
    calc C₁ = C₁ * 1 := by ring
      _ ≤ C₁ * (1 + C) := mul_le_mul_of_nonneg_left h1_le_1pC hC₁_nn
  have hfact_pos : (0 : ℝ) < ((2 * k n + 1).factorial : ℝ) := by
    have : 0 < (2 * k n + 1).factorial := Nat.factorial_pos _
    exact_mod_cast this
  have hpow_nn :
      (0 : ℝ) ≤ (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1) :=
    pow_nonneg (by exact_mod_cast Nat.zero_le _) _
  -- Common factor T_n
  set T_n : ℝ := (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ) with hT_def
  have hT_nn : 0 ≤ T_n := by
    rw [hT_def]; exact div_nonneg (mul_nonneg hn_nn hpow_nn) (le_of_lt hfact_pos)
  have hErr_orig_eq :
      C₁ * (n : ℝ)
          * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
          / ((2 * k n + 1).factorial : ℝ)
        = C₁ * T_n := by
    rw [hT_def]; ring
  have hErr_target_eq :
      C₁ * (1 + C) * (n : ℝ)
          * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
          / ((2 * k n + 1).factorial : ℝ)
        = C₁ * (1 + C) * T_n := by
    rw [hT_def]; ring
  have hErr_bound : C₁ * T_n ≤ C₁ * (1 + C) * T_n :=
    mul_le_mul_of_nonneg_right hC₁_le hT_nn
  -- Combine.
  have hSiftSelbergRHS :
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * M (Nat.sqrt n) + C₁ * T_n := by
    have := hbound n hn
    rw [hErr_orig_eq] at this
    exact this
  -- Now combine the two pieces:
  --   ≤ C₁(1+C) n pBF(√n) + C₁(1+C) T_n
  calc (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ C₁ * (n : ℝ) * M (Nat.sqrt n) + C₁ * T_n := hSiftSelbergRHS
    _ ≤ C₁ * (1 + C) * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
        + C₁ * (1 + C) * T_n := add_le_add hMain hErr_bound
    _ = C₁ * (1 + C) * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
        + C₁ * (1 + C) * (n : ℝ)
            * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
            / ((2 * k n + 1).factorial : ℝ) := by
        rw [hErr_target_eq]

/-! ## Section 5 — The reverse direction (Brun ⇒ Selberg-shape)

By symmetry, a Brun-shape bound can be re-expressed as a Selberg-shape
bound provided the *other* direction of the factor equivalence is
available, namely `pairedBrunFactor ≤ C · M`.  This is the direction
that lets us *upper-bound* the Brun factor by the Selberg factor.

In sieve theory these two directions are equivalent (up to constants;
both Selberg and Brun give bounded ratios `M/pairedBrunFactor` and
`pairedBrunFactor/M`), but each direction must be proved separately.
-/

/-- **The Brun-to-Selberg factor equivalence (upper direction).**

For the paired Goldbach density, `pairedBrunFactor(z) ≤ C · M(z)` for
some `C > 0`.  Together with `M ≤ C · pairedBrunFactor` (the reverse),
this is the *full* equivalence of Brun and Selberg main-term factors. -/
def MathlibSelbergBrunFactorEquivalence (M : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, pairedBrunFactor z ≤ C * M z

/-! ## Section 6 — Gap analysis: what would close the residuals via
Selberg

The Selberg route would close `AlignedInequalityAndTail` provided:

(A) `SelbergPairedGoldbachBound M_sel` for the Selberg main-term factor
    `M_sel(z) = 1 / V(z)` for the paired Goldbach density `ν(p) = 2/p`.
    **Status in mathlib v4.29.1:**  the assembly skeleton exists
    (`Mathlib.NumberTheory.SelbergSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`)
    but the concrete `M_sel` is not constructed, the Λ² weights are
    not assembled, and the resulting `mainSum`/`errSum` are not bounded.
    This is **multi-thousand-line Halberstam-Richert §4 material**.

(B) `MathlibBrunSelbergFactorEquivalence M_sel`:  `M_sel(z) ≤ C ·
    pairedBrunFactor(z)`.  **Status in mathlib v4.29.1:**  open.
    The Mertens product estimate `∏_{p ≤ z}(1 - 2/p) ≪ 1/(log z)^2`
    is itself the **`PairedBrunMertensThirdGap`** Prop in our
    `PathC_BrunGoldbachComposition.lean` — open!

(C) The tail-alignment with `refinedReservoir` (the second clause of
    `AlignedInequalityAndTail`).  **Status:**  even granting (A) and (B),
    the Selberg-error term has a *different* shape from Brun-Bonferroni
    (involving the τ_3 function vs. `π(z)^k / k!`), so this clause
    requires its own analytic argument.

Quantitative summary:  **Selberg in mathlib v4.29.1 is no closer to
closing `AlignedInequalityAndTail` than Brun-Bonferroni.**  The two
routes share the same Mertens residual (`PairedBrunMertensThirdGap`),
and Selberg adds the additional cost of constructing Λ² weights.

Therefore the **manual Brun-Bonferroni route** of P19-T14 / P19-T16
is, for now, the more tractable route.

We expose the gap analysis as a single bundled Prop. -/

/-- **The bundled Selberg gap.**

The Selberg route would close `AlignedInequalityAndTail` iff *all four*
sub-Props are available:

1. `SelbergPairedGoldbachBound M`:  the paired-sift Selberg main bound.
2. `MathlibBrunSelbergFactorEquivalence M`:  the upper-equivalence
   `M ≤ C · pairedBrunFactor`.
3. The tail-absorption inequality
   `∀ n, N ≤ n → C₂ · n · (π(√n))^(2k+1)/(2k+1)! ≤ refinedReservoir n (√n)`
   (this is the same tail clause as in `AlignedInequalityAndTail`,
   *not* an additional hypothesis specific to Selberg; the P19-T5-Sqrt
   route already closes it via `pairedBonferroniTailAtSqrt_holds`,
   which delivers a Prop of essentially this exact shape).
4. The constants match (`C₂` from clause 3 ≤ scaled `C₁` from the
   Selberg main bound).

We expose the *first two* as the genuinely **Selberg-specific**
residuals; the third is shared with Brun.  Closing 1 and 2 gives the
inequality clause of `AlignedInequalityAndTail` up to the alignment
constant scaling, which is mechanical. -/
def SelbergRouteSelbergSpecificResiduals : Prop :=
  ∃ M : ℕ → ℝ,
    SelbergPairedGoldbachBound M ∧ MathlibBrunSelbergFactorEquivalence M

/-! ## Section 7 — Conditional theorem: Selberg-specific residuals ⇒
the inequality clause of `AlignedInequalityAndTail`

Provided we *have* the Selberg-specific residuals
(`SelbergRouteSelbergSpecificResiduals`), and provided we also have the
*tail-absorption* clause from `AlignedInequalityAndTail` separately
(which is closed unconditionally by P19-T5-Sqrt), then we can assemble
the full `AlignedInequalityAndTail` Prop. -/

/-- **The inequality clause of `AlignedInequalityAndTail` follows from
the Selberg-specific residuals.**

`SelbergRouteSelbergSpecificResiduals` delivers an inequality of the
shape

```
goldbachSiftedPair n (√n)
  ≤ C₂ · n · pairedBrunFactor(√n)
  + C₂ · n · (π(√n))^(2k+1)/(2k+1)!
```

for some `C₂ > 0`, `N ≥ 4`, and a truncation depth function `k : ℕ → ℕ`. -/
theorem inequalityClause_of_selbergRouteSelbergSpecificResiduals
    (h : SelbergRouteSelbergSpecificResiduals) :
    ∃ C₂ : ℝ, ∃ N : ℕ, ∃ k : ℕ → ℕ,
      0 < C₂ ∧ 4 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C₂ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + C₂ * (n : ℝ)
                * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ) := by
  obtain ⟨M, hSelberg, hRev⟩ := h
  exact brunFactor_shape_inequality_of_selberg M hSelberg hRev

/-! ## Section 8 — Honest conclusion

The Selberg route in mathlib v4.29.1 is **not closer** to closing
`AlignedInequalityAndTail` than the manual Brun-Bonferroni route.  Both
routes ultimately reduce to:

(i) A Mertens-type product estimate (open in mathlib for paired
    densities — this is the `PairedBrunMertensThirdGap` Prop we
    already expose in `PathC_BrunGoldbachComposition.lean`).

(ii) A truncation-error estimate (open in mathlib — for Brun this is
    `(π(z))^k / k!`, for Selberg it is `∑_{d ≤ z²} 3^{ω(d)} |r_d|`).

(iii) A factor-equivalence (open in mathlib — `M ≍ pairedBrunFactor`).

The Selberg sieve in mathlib only provides the *assembly skeleton*
(`siftedSum_le_mainSum_errSum_of_upperMoebius`); the concrete Λ²
weights, Mertens estimates, and equivalence-of-sieves constants are
not formalised.

Therefore P19-T14 / P19-T16 (manual paired Brun-Bonferroni at `k = 2n`)
remain the **primary route** to closing the residuals.  The Selberg
route is *equivalent* in difficulty, not strictly easier.

We record this conclusion as a Prop-level claim: there is **no
shortcut via mathlib's existing Selberg sieve** that avoids the same
analytic residuals that block the Brun route. -/

/-- **Honest conclusion (no-shortcut claim).**

For *any* main-term factor `M`, the Selberg-shape paired Goldbach
bound `SelbergPairedGoldbachBound M` combined with the upper
factor-equivalence `MathlibBrunSelbergFactorEquivalence M` together
suffice to produce a Brun-shape inequality (as proved in
`brunFactor_shape_inequality_of_selberg`).

But the *combination* `SelbergPairedGoldbachBound M ∧
MathlibBrunSelbergFactorEquivalence M` is itself **at least as hard**
to establish as the Brun route's interior residual
`PairedBonferroniInequalityAtSqrtAlignedWithTail`, because:

* `SelbergPairedGoldbachBound M` requires constructing Λ² weights and
  bounding `mainSum + errSum` over the paired Goldbach density.

* `MathlibBrunSelbergFactorEquivalence M` requires the Mertens product
  estimate `∏_{p ≤ z}(1 - 2/p) ≍ 1/(log z)²`, which is exactly the
  Mertens-third-gap content also needed for Brun.

This theorem records the trivial statement that the two Selberg-
specific residuals together imply the inequality clause of
`AlignedInequalityAndTail`, with the unconditional caveat that
*proving* those residuals from mathlib v4.29.1 is at least as much
work as proving the Brun-Bonferroni inequality directly. -/
theorem selberg_route_no_shortcut
    (h : SelbergRouteSelbergSpecificResiduals) :
    ∃ C₂ : ℝ, ∃ N : ℕ, ∃ k : ℕ → ℕ,
      0 < C₂ ∧ 4 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C₂ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + C₂ * (n : ℝ)
                * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ) :=
  inequalityClause_of_selbergRouteSelbergSpecificResiduals h

/-! ## Section 9 — Verifying mathlib's framework is non-vacuous

A sanity check: any `BoundingSieve` admits *at least one* upper-Möbius
weight, namely the constant `muPlus 1 = 1` and `muPlus d = 0` for `d > 1`.
This is just the trivial "sum at `n = 1`" recovery, but it confirms the
framework is non-vacuous. -/

/-- The trivial upper-Möbius weight: `1` at `d = 1`, `0` elsewhere.
This satisfies `IsUpperMoebius` because the bound `[n = 1] ≤ ∑_{d ∣ n}
muPlus(d)` reduces to `[n = 1] ≤ muPlus(1) · [1 ∣ n] = 1`, which is
true at `n = 1` (and vacuous otherwise). -/
def trivialUpperMoebius : ℕ → ℝ := fun d => if d = 1 then 1 else 0

/-- The trivial weight is upper-Möbius. -/
theorem trivialUpperMoebius_isUpperMoebius :
    IsUpperMoebius trivialUpperMoebius := by
  intro n
  -- Need: [n=1] ≤ ∑ d ∈ n.divisors, trivialUpperMoebius d
  -- Right side equals 1 if n ≥ 1 (since 1 ∈ divisors n) and contains
  -- 1 if and only if n ≠ 0. We need:
  --   if n = 1 then 1 ≤ RHS else 0 ≤ RHS.
  by_cases hn : n = 1
  · subst hn
    -- divisors 1 = {1}; muPlus(1) = 1; sum = 1.
    simp [trivialUpperMoebius]
  · -- LHS = 0.  RHS = ∑ d ∈ n.divisors, [d = 1] (as real).  This is
    --   0 if 1 ∉ divisors n (i.e. n = 0) and 1 otherwise, but in
    --   either case ≥ 0.
    simp only [if_neg hn]
    -- We want 0 ≤ ∑ d ∈ n.divisors, if d = 1 then 1 else 0.
    apply Finset.sum_nonneg
    intro d _
    unfold trivialUpperMoebius
    by_cases hd : d = 1
    · rw [if_pos hd]; norm_num
    · rw [if_neg hd]

/-- **Sanity check:**  for any `BoundingSieve s`, mathlib's
`siftedSum_le_mainSum_errSum_of_upperMoebius` applied to the trivial
weight gives the (uninformative) bound `siftedSum ≤ totalMass * nu 1 +
|rem 1|`.  This is `totalMass + |multSum 1 - totalMass|`, an utter
triviality — but it confirms the framework's delivery theorem is at
least *applicable* without further hypotheses. -/
theorem mathlib_trivial_application (s : BoundingSieve) :
    s.siftedSum
      ≤ s.totalMass * s.mainSum trivialUpperMoebius
        + s.errSum trivialUpperMoebius :=
  mathlib_selberg_delivers s trivialUpperMoebius trivialUpperMoebius_isUpperMoebius

/-! ## Section 10 — Summary of deliverables

This file:

* **Documents** that `Mathlib.NumberTheory.SelbergSieve` delivers
  exactly one quantitative theorem
  (`siftedSum_le_mainSum_errSum_of_upperMoebius`) and is otherwise a
  Prop-level assembly skeleton.

* **Defines** the Selberg-shape paired Goldbach Prop
  `SelbergPairedGoldbachBound`.

* **Defines** the two-directional factor equivalence Props
  `MathlibBrunSelbergFactorEquivalence` and
  `MathlibSelbergBrunFactorEquivalence`.

* **Proves**  the mechanical bridge
  `brunFactor_shape_inequality_of_selberg`:  Selberg-shape bound +
  reverse equivalence ⇒ Brun-shape inequality clause of
  `AlignedInequalityAndTail`.

* **Records** the gap analysis: the Selberg route in mathlib v4.29.1
  is *no easier* than the Brun-Bonferroni route, because both share
  the open Mertens product estimate
  (`PairedBrunMertensThirdGap`) and require equivalent analytic work.

* **Concludes** honestly:  P19-T14 / P19-T16 (manual paired
  Brun-Bonferroni) remain the primary route to closing
  `AlignedInequalityAndTail` and
  `PairedBonferroniNaturalSubSqrtCombinatorialKernel`.

All theorems and definitions axiom-clean: only `Classical.choice`,
`Quot.sound`, `propext`. -/

end PathCSelbergRoute
end Gdbh
