/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P26-T3 (Phase 26 / Path C — Bridge to the
        `goldbachLocalFactor` identity for the paired Brun-Goldbach
        sieve, at the canonical sieve level `z = Nat.sqrt n`).
-/
import Gdbh.PathC_GoldbachLocalFactor
import Gdbh.PathC_PairedBonferroniIndicator
import Gdbh.PathC_PairedBonferroniSumRearrange
import Gdbh.PathC_GoldbachPairCRTCount
import Gdbh.PathC_PairedMainTermAtSqrtReduction
import Gdbh.PathC_PairedMainTermFromLocalDensity

/-!
# Path C — P26-T3: Bridge to the `goldbachLocalFactor` identity

This file is the **P26-T3 deliverable** in Phase 26 (Path C closure).
Its target is the *layer 2* bridge in the HL §3.11 master expansion:

```
   goldbachSiftedPair n (Nat.sqrt n)
     ≤  C · n · goldbachLocalFactor n (Nat.sqrt n)  +  (truncation error)
```

## Layer structure

The HL §3.11 master expansion for the Brun-Goldbach upper bound passes
through three layers:

* **Layer 0** — the trivial cardinal bound
  `goldbachSiftedPair n z ≤ n`, with worst-case error `B(n, z) := n`.
  This is closed in `PathC_GoldbachRBound.brunGoldbachMainTerm_trivial_witness`.

* **Layer 1** — the *uniform* paired Brun factor bound
  `goldbachSiftedPair n z ≤ C₁ · n · pairedBrunFactor(z) + refinedReservoir(n,z)`.
  This is the named open `BrunGoldbachPairedMainTermRefined` Prop from
  `PathC_BrunRefinedComposition`.

* **Layer 2** — the *`n`-dependent* honest local-factor bound
  `goldbachSiftedPair n z ≤ C · n · goldbachLocalFactor(n, z) + (tail)`,
  reflecting the fact that for primes `p ∣ n` the two forbidden residue
  classes `m ≡ 0` and `m ≡ n` modulo `p` *coincide*, so only one residue
  is forbidden (not two).  This is the named open
  `BrunGoldbachLocalMainTermRefined` Prop from
  `PathC_GoldbachLocalFactor`.

This file assembles **Layer 2** *conditionally* on three named Props
that encapsulate the genuine analytic content delivered by P25-T2,
P26-T2, and the truncation-tail estimate.

## What is closed (axiom-clean)

* `LocalFactorBridgeHypothesis` — a single named Prop bundling the
  three hypothetical inputs delivered by P25-T2, P26-T2, and the
  truncation tail estimate, presented in the shape that combines
  algebraically into the local-factor bound at sieve level `z = √n`.

* `goldbachSiftedPair_le_local_factor_plus_error` — the *conditional*
  Layer 2 bridge.  Given an instance of `LocalFactorBridgeHypothesis`,
  this theorem produces the honest output shape

  ```
  (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
    ≤ C * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
        + refinedReservoir n (Nat.sqrt n)
  ```

  for every `n ≥ N₀` (with `N₀ ≥ 2`).

* `localFactorBridgeHypothesis_of_refined_paired` — a *trivial bridge*
  showing that the existing uniform-factor Prop
  `BrunGoldbachPairedMainTermRefined` already supplies enough algebraic
  structure to populate `LocalFactorBridgeHypothesis` (through the
  pointwise inequality
  `pairedBrunFactor_le_goldbachLocalFactor`).  This is a *witness check*
  for the bridge's well-formedness: any future closure of the uniform
  Prop automatically yields the honest local-factor output.

## Honesty disclosure

The truncation-tail content (`PairedMainTermFromLocalDensity`, P17-T4)
is open in mathlib v4.29.1 — see
`PathC_PairedMainTermFromLocalDensity.lean`.  The closure of the paired
CRT counting kernel `GoldbachPairCRTCount` is *complete* in
`PathC_GoldbachPairCRTCount` for *coprime* divisor pairs; the
gcd-split refinement `goldbachPairCount_split` from
`PathC_PairedCRTSplitByGCD` is partially closed (the
`d ∣ n` branch contains one residual `sorry` for the divisor-counting
identity `(n - 1)/d = n/d - 1`).

Because this file *does not* close any of those open Props itself, but
merely *bridges* the conditional Layer 2 output assuming them as
hypotheses, the bridge theorem is **axiom-clean** (transitively only
`Classical.choice`, `Quot.sound`, `propext`).

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`,
`Quot.sound`, and `propext` are transitively used.  No `sorry`,
`axiom`, or `admit` appears.

## Theorem names exported

* `Gdbh.PathCGoldbachLocalFactorBridge.LocalFactorBridgeHypothesis`
  — the named Prop bundling the conditional inputs.
* `Gdbh.PathCGoldbachLocalFactorBridge.goldbachSiftedPair_le_local_factor_plus_error`
  — the conditional Layer 2 bridge.
* `Gdbh.PathCGoldbachLocalFactorBridge.localFactorBridgeHypothesis_of_refined_paired`
  — trivial inhabitation from the uniform-factor Prop
  `BrunGoldbachPairedMainTermRefined`.
-/

namespace Gdbh
namespace PathCGoldbachLocalFactorBridge

open scoped BigOperators
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos)
open Gdbh.PathCGoldbachRBound (goldbachSiftedPair)
open Gdbh.PathCBrunRefinedComposition (refinedReservoir refinedReservoir_def
  BrunGoldbachPairedMainTermRefined)
open Gdbh.PathCGoldbachLocalFactor (goldbachLocalFactor goldbachLocalFactor_pos
  pairedBrunFactor_le_goldbachLocalFactor
  BrunGoldbachLocalMainTermRefined)

/-! ## Section 1 — Conditional input Prop

The local-factor bridge requires three independent inputs:

1. A **uniform Brun-Goldbach paired main-term inequality at the sqrt
   threshold**, of the shape

   ```
   (goldbachSiftedPair n √n : ℝ)
     ≤ C₁ · n · pairedBrunFactor(√n) + refinedReservoir n √n .
   ```

   This is exactly the `BrunGoldbachPairedMainTermRefined` Prop
   specialised at `z = Nat.sqrt n`.

2. The **paired CRT splitting by `gcd(d, n)`** (P25-T2): the count
   `#{m ∈ [1, n-1] : d ∣ m ∧ d ∣ (n - m)}` is zero when `d ∤ n` and
   equals `n/d - 1` when `d ∣ n`.  This is the splitting that
   distinguishes the `n`-dependent local density from the uniform
   paired Brun factor.

3. The **local-density Euler product identity** (P26-T2): the
   `n`-dependent local factor `goldbachLocalFactor(n, z)` is the
   uniform paired factor `pairedBrunFactor(z)` multiplied by the
   *truncated Goldbach singular multiplier*

   ```
   ∏ p∈[3,z], p prime, p ∣ n,  (1 + 1/(p-2)) ,
   ```

   which is `≥ 1` (closed unconditionally in
   `PathC_GoldbachLocalFactor.truncatedGoldbachSingularMultiplier_ge_one`).

In our bridge, we *only* need input #1 and the *unconditional* part of
input #3 (the pointwise inequality
`pairedBrunFactor ≤ goldbachLocalFactor`).  Input #2 enters only
implicitly, through the genuine *closure* of input #1 (which is
P25-T2's job, not this file's).

We package input #1 as the named `Prop` `LocalFactorBridgeHypothesis`.
-/

/-- **Local-factor bridge hypothesis (P26-T3).**

The conditional input for the Layer 2 bridge: a uniform Brun-Goldbach
paired main-term inequality holding for all `n ≥ N₀` (with `N₀ ≥ 2`),
at the canonical sieve level `z = Nat.sqrt n`, with the uniform paired
Brun factor and the refined reservoir.

This is the *uniform*-factor specialisation; the bridge will *upgrade*
it to the `n`-dependent local-factor inequality via the unconditional
pointwise dominance
`pairedBrunFactor(z) ≤ goldbachLocalFactor(n, z)`. -/
def LocalFactorBridgeHypothesis : Prop :=
  ∃ C₁ : ℝ, ∃ N₀ : ℕ, 0 < C₁ ∧ 2 ≤ N₀ ∧
    ∀ n : ℕ, N₀ ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + refinedReservoir n (Nat.sqrt n)

/-! ## Section 2 — The conditional Layer 2 bridge

Given the conditional uniform-factor hypothesis, the local-factor
bridge follows by *increasing* the uniform paired factor to the
honest `n`-dependent local factor.  Since
`pairedBrunFactor(z) ≤ goldbachLocalFactor(n, z)` (unconditional, see
`PathC_GoldbachLocalFactor.pairedBrunFactor_le_goldbachLocalFactor`),
multiplying both sides by the non-negative weight `C₁ · n` preserves
the inequality.
-/

/-- **Layer 2 bridge (conditional on the uniform-factor input).**

Given an instance of `LocalFactorBridgeHypothesis` (i.e. an absolute
constant `C₁ > 0`, a threshold `N₀ ≥ 2`, and a uniform paired-sieve
bound holding for all `n ≥ N₀`), there is an absolute constant
`C := C₁ > 0` such that for all `n ≥ N₀`,

```
(goldbachSiftedPair n √n : ℝ)
  ≤ C · n · goldbachLocalFactor(n, √n) + refinedReservoir n √n .
```

This is the **layer 2** form of the HL §3.11 master expansion: the
honest `n`-dependent local-density structure with truncation error.

The proof is a one-line consequence of the pointwise dominance
`pairedBrunFactor ≤ goldbachLocalFactor` together with non-negativity
of `C₁ · n`. -/
theorem goldbachSiftedPair_le_local_factor_plus_error
    (hHyp : LocalFactorBridgeHypothesis) :
    ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 2 ≤ N₀ ∧
      ∀ n : ℕ, N₀ ≤ n →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
              + refinedReservoir n (Nat.sqrt n) := by
  classical
  -- Unpack the conditional hypothesis.
  rcases hHyp with ⟨C₁, N₀, hC₁_pos, hN₀, hMain⟩
  refine ⟨C₁, N₀, hC₁_pos, hN₀, ?_⟩
  intro n hn
  -- Apply the uniform bound at this `n`.
  have hbd := hMain n hn
  -- Pointwise dominance: `pairedBrunFactor √n ≤ goldbachLocalFactor n √n`.
  have hfactor :
      pairedBrunFactor (Nat.sqrt n)
        ≤ goldbachLocalFactor n (Nat.sqrt n) :=
    pairedBrunFactor_le_goldbachLocalFactor n (Nat.sqrt n)
  -- Multiply both sides by the non-negative weight `C₁ · n`.
  have hweight_nn : 0 ≤ C₁ * (n : ℝ) := by
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    exact mul_nonneg (le_of_lt hC₁_pos) hn_nn
  have hupgrade :
      C₁ * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
        ≤ C₁ * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n) :=
    mul_le_mul_of_nonneg_left hfactor hweight_nn
  -- Chain through the uniform bound.
  linarith

/-! ## Section 3 — Trivial inhabitation from the uniform-factor Prop

The conditional hypothesis `LocalFactorBridgeHypothesis` is *strictly
weaker* than the named open Prop `BrunGoldbachPairedMainTermRefined`
(which is the uniform-factor inequality *over all `z`*, not only at
`z = √n`).  Any closure of `BrunGoldbachPairedMainTermRefined` therefore
automatically populates `LocalFactorBridgeHypothesis`.

This shows the bridge is *well-formed*: there is no circular dependency
or unstated additional hypothesis. -/

/-- **Trivial bridge: `BrunGoldbachPairedMainTermRefined` populates the
local-factor bridge hypothesis.**

Given the uniform-factor Prop holding for all `z`, specialising at
`z = Nat.sqrt n` and `N₀ = 2` produces an instance of
`LocalFactorBridgeHypothesis`. -/
theorem localFactorBridgeHypothesis_of_refined_paired
    (hMain : BrunGoldbachPairedMainTermRefined) :
    LocalFactorBridgeHypothesis := by
  -- Unpack the refined paired main-term Prop.
  rcases hMain with ⟨_hFactor, C₁, hC₁_pos, hbd⟩
  refine ⟨C₁, 2, hC₁_pos, le_refl 2, ?_⟩
  intro n hn
  -- The Prop `BrunGoldbachPairedMainTermRefined` is universal in `z ≥ 0`;
  -- specialise at `z = Nat.sqrt n`.
  exact hbd n (Nat.sqrt n) (by omega)

/-! ## Section 4 — Composed bridge: from uniform-factor to local-factor

Combining the two preceding theorems yields the *direct* bridge from
`BrunGoldbachPairedMainTermRefined` to the local-factor inequality at
`z = √n`.  This is the precise conditional shape requested by the
P26-T3 task statement.
-/

/-- **Composed Layer 2 bridge.**

The uniform-factor Prop `BrunGoldbachPairedMainTermRefined` directly
implies the existential local-factor inequality at `z = √n`. -/
theorem goldbachSiftedPair_le_local_factor_plus_error_of_refined
    (hMain : BrunGoldbachPairedMainTermRefined) :
    ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 2 ≤ N₀ ∧
      ∀ n : ℕ, N₀ ≤ n →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
              + refinedReservoir n (Nat.sqrt n) :=
  goldbachSiftedPair_le_local_factor_plus_error
    (localFactorBridgeHypothesis_of_refined_paired hMain)

/-! ## Section 5 — Targeted bridge: `BrunGoldbachLocalMainTermRefined`
already in `PathC_GoldbachLocalFactor`

The named Prop `BrunGoldbachLocalMainTermRefined` from
`PathC_GoldbachLocalFactor` is essentially the local-factor inequality
*for all `z`*.  We provide a bridge that *also* delivers the same
existential output, packaged for downstream consumers that expect the
local-factor sub-Prop directly. -/

/-- **Targeted bridge from `BrunGoldbachLocalMainTermRefined`.**

The named open `BrunGoldbachLocalMainTermRefined` Prop already states
the local-factor inequality for all `z`; specialising at
`z = Nat.sqrt n` produces the existential output of the Layer 2
bridge. -/
theorem goldbachSiftedPair_le_local_factor_plus_error_of_localMain
    (hMain : BrunGoldbachLocalMainTermRefined) :
    ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 2 ≤ N₀ ∧
      ∀ n : ℕ, N₀ ≤ n →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ C * (n : ℝ) * goldbachLocalFactor n (Nat.sqrt n)
              + refinedReservoir n (Nat.sqrt n) := by
  rcases hMain with ⟨C₁, hC₁_pos, hbd⟩
  refine ⟨C₁, 2, hC₁_pos, le_refl 2, ?_⟩
  intro n hn
  -- `BrunGoldbachLocalMainTermRefined` is universal in `z ≥ 0`;
  -- specialise at `z = Nat.sqrt n`.
  exact hbd n (Nat.sqrt n) (by omega)

/-! ## Section 6 — Documentation of *upstream* genuine residual content

The P26-T3 bridge is **conditional** on `LocalFactorBridgeHypothesis`,
which is the named open Prop encoding the *genuine* analytic content
shared with `BrunGoldbachPairedMainTermRefined`.

The honest residual gap that remains *upstream* of the bridge is:

* **P25-T2** (`PathC_PairedCRTSplitByGCD`): paired CRT counting with
  the gcd split.  The `d ∤ n` branch is fully closed
  (`goldbachPairCount_split_zero_of_not_dvd`).  The `d ∣ n` branch
  reduces (axiom-cleanly) to the single divisor-counting identity
  `(n - 1)/d = n/d - 1`, which is genuinely classical.  Status:
  in-progress.

* **P26-T2** (`PathC_GoldbachLocalFactor`):  the *Euler-product
  pointwise factorisation* of `goldbachLocalFactor` is closed
  unconditionally (`goldbachLocalFactor_eq_paired_mul_singularMultiplier`)
  along with the dominance
  (`pairedBrunFactor_le_goldbachLocalFactor`).  Status: closed.

* **Truncation tail** (`PathC_PairedMainTermFromLocalDensity`):  the
  classical Bonferroni-Brun inequality controlling the truncated
  alternating-sum tail in `BrunGoldbachPairedMainTermRefined`.  Status:
  open as the named Prop `PairedMainTermFromLocalDensity`.

The combinatorial pieces — the *paired Bonferroni indicator inequality*
(P19-T1, `pairedBonferroniIndicator_holds`) and the *paired Bonferroni
sum rearrangement* (P19-T3, `pairedBonferroniSumRearrange_holds`) — are
both closed unconditionally and feed into the proof of
`LocalFactorBridgeHypothesis` once the truncation-tail Prop is closed.

## How this file slots into the master expansion

After this bridge, the next layer (Layer 3) of HL §3.11 master would
be the *singular-series specialisation*:

```
goldbachLocalFactor(n, √n)  =  pairedBrunFactor(√n)
                                · truncatedGoldbachSingularMultiplier(n, √n) .
```

This is *already closed* in `PathC_GoldbachLocalFactor` as
`goldbachLocalFactor_eq_paired_mul_singularMultiplier`.  Combined with
the singular-series identification of
`truncatedGoldbachSingularMultiplier(n, √n) ≈ goldbachSingularMultiplier n`
(open as a quantitative estimate, separate task), this delivers the
final HL §3.11 master output

```
  goldbachSiftedPair n √n  ≤  C · n · pairedBrunFactor(√n)
                                 · goldbachSingularMultiplier n
                              + (controlled error) .
```
-/

/-- **P26-T3 summary, in proof form.**

The Layer 2 bridge is closed axiom-cleanly **conditional** on
`LocalFactorBridgeHypothesis`, which is itself supplied by *any* closure
of the uniform-factor Prop `BrunGoldbachPairedMainTermRefined` (or the
local-factor Prop `BrunGoldbachLocalMainTermRefined`).  The bridge
upgrades the uniform paired Brun factor to the honest `n`-dependent
local factor using the unconditional pointwise inequality
`pairedBrunFactor_le_goldbachLocalFactor`.

No `sorry`, `axiom`, or `admit` is introduced by this file. -/
theorem pathC_p26_t3_summary : True := trivial

end PathCGoldbachLocalFactorBridge
end Gdbh
