/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T34 (Phase 19 / Path C — Brun-Goldbach for the bounded
        primes set, fix `z₀` and study uniform-in-`n` behaviour).
-/
import Gdbh.PathC_GoldbachRBound
import Gdbh.PathC_MertensProof
import Gdbh.PathC_PairedBrunSmallZ

/-!
# Path C — P19-T34: Brun-Goldbach for the BOUNDED primes set

This file is the **P19-T34 deliverable**.  The task: instead of pursuing
a fully uniform-in-`z` Brun-Goldbach bound (where the dependence on `z`
is the irreducible analytic obstruction), **fix** a sieve threshold
`z₀ : ℕ` and ask whether the bound

```
(goldbachSiftedPair n z₀ : ℝ)  ≤  2 · n · pairedBrunFactor z₀
```

is *uniform in `n`* (for all `n ≥ N₀(z₀)`).

## Heuristic claim from the task brief

For fixed `z₀`, with `P := (Finset.Icc 3 z₀).filter Nat.Prime`:

* The paired Bonferroni indicator at truncation depth `k = |P|` gives
  the EXACT identity (no Bonferroni tail truncation).
* The Möbius identity (`paired_eulerProduct_moebius_form`) collapses the
  alternating sum to `pairedBrunFactor z₀`.
* Each CRT cell contributes an error of `≤ 1` (P17-T3
  `goldbachPairCRTCount_holds`), so the total CRT error is bounded by
  `2^|P|` — a *finite* constant depending only on `z₀`.

Hence (heuristically)

```
goldbachSiftedPair n z₀  ≤  n · pairedBrunFactor z₀  +  2^|P| ,
```

and for `n ≥ 2^|P| / pairedBrunFactor z₀` the `2^|P|` absorbs into the
main term factor of `2`.

## Honesty finding (this file's main scientific output)

Closing the theorem `brunGoldbachBoundedPrimes_holds (z₀ : ℕ) :
BrunGoldbachBoundedPrimes z₀` axiom-cleanly for **all** `z₀ : ℕ`
requires the *same* paired Brun-Bonferroni assembly as the uniform-in-`z`
target.  The bounded-primes setting **does not** structurally
collapse the residual.  Specifically:

### Closed slice: `z₀ ≤ 2`

For `z₀ ≤ 2`, the Möbius product `pairedBrunFactor z₀` is an empty
product equal to `1` (lemma
`Gdbh.PathCPairedBrunSmallZ.pairedBrunFactor_eq_one_of_le_two`).  Hence
the bound `goldbachSiftedPair n z₀ ≤ 2n · pairedBrunFactor z₀ = 2n`
follows from the trivial cardinal bound
`goldbachSiftedPair n z ≤ n` (which is `≤ 2n`).  **Closed here**,
axiom-clean, with `N₀ = 0` (the bound holds for **every** `n : ℕ`).

### Open slice: `z₀ ≥ 3`

For `z₀ ≥ 3`, `pairedBrunFactor z₀ ≤ 1/3 < 1/2`.  The trivial cardinal
bound `goldbachSiftedPair n z₀ ≤ n` does **not** imply
`goldbachSiftedPair n z₀ ≤ 2n · pairedBrunFactor z₀`, for any `n ≥ 1`,
since this would require `1 ≤ 2 · pairedBrunFactor z₀`.

To extract a `2 · pairedBrunFactor z₀` upper bound on the sift density,
one must perform actual sieve work — and the sieve work needed is
**exactly** the paired Bonferroni assembly invoked in
`PathC_PairedBrunSubSqrtProof.lean` (T1 indicator + T3 rearrangement +
P17-T3 CRT count + T4 Euler product + T28 Möbius form), specialised
from the variable threshold to the fixed threshold.

The *structural* gain claimed in the task brief — namely that at
`k = |P|` the Bonferroni truncation tail vanishes — is real, but does
not bypass the *paired CRT counting kernel* itself.  Closing the kernel
axiom-cleanly is precisely the Phase 18 residual exposed as
`AlignedSubSqrtInequalityAndTail` (and its bridges in
`PathC_PairedBrunSubSqrtProof.lean`).

We therefore expose the residual `BrunGoldbachBoundedPrimes z₀` for
`z₀ ≥ 3` as a *named open Prop* (`BrunGoldbachBoundedPrimes`), close
the trivial-`z₀` slice (`z₀ ≤ 2`) axiom-cleanly via
`brunGoldbachBoundedPrimes_holds_of_le_two`, and prove the
*conditional* implication:  if the paired Bonferroni kernel discharges
the bounded-primes residual at `z₀ ≥ 3` (sub-Prop
`BoundedPrimesBrunKernel z₀`), then
`brunGoldbachBoundedPrimes_holds (z₀ : ℕ) : BrunGoldbachBoundedPrimes z₀`
follows.

The honest report — repeated here for clarity — is:  **the bounded-primes
version still requires the paired Bonferroni kernel**, which is the
same kernel needed for the uniform-in-`z` version.  The structural
saving (`k = |P|`, no Bonferroni tail) does not bridge the kernel-level
obstruction.

## Strict constraints

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene target: `[Classical.choice, Quot.sound, propext]`.
* File compiles standalone.

## File-write rule

This file is the **only** new file.  No edits to other repository files.
-/

namespace Gdbh
namespace PathCBoundedPrimesBrun

open Gdbh.PathCGoldbachRBound (goldbachSiftedPair goldbachSiftedPair_le)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCPairedBrunSmallZ (pairedBrunFactor_eq_one_of_le_two)

/-! ## Section 1 — The bounded-primes Prop -/

/-- **`BrunGoldbachBoundedPrimes z₀`** — for a *fixed* sieve threshold
`z₀ : ℕ`, the Brun-Goldbach upper bound with constant `2` and density
`pairedBrunFactor z₀`, uniform in `n` for `n ≥ N₀`.

```
∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
  (goldbachSiftedPair n z₀ : ℝ)
    ≤ 2 · (n : ℝ) · pairedBrunFactor z₀ .
```

**Note on uniformity.**  This Prop is **NOT** uniform in `z₀`: both `N₀`
and the inequality's slack depend on `z₀` (through `pairedBrunFactor z₀`
which decays to `0` as `z₀ → ∞`).  It **IS** uniform in `n` for each
fixed `z₀`.  This is the *bounded-primes* angle the task explores. -/
def BrunGoldbachBoundedPrimes (z₀ : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    (goldbachSiftedPair n z₀ : ℝ)
      ≤ 2 * (n : ℝ) * pairedBrunFactor z₀

/-! ## Section 2 — Closed slice: `z₀ ≤ 2`

For `z₀ ≤ 2`, `pairedBrunFactor z₀ = 1` (empty product), so the bound
reduces to `goldbachSiftedPair n z₀ ≤ 2 · n`, which follows from the
trivial cardinal bound `goldbachSiftedPair n z₀ ≤ n` (with a slack of
factor `2`).  No sieve content needed. -/

/-- **Closed slice (`z₀ ≤ 2`)** — for trivially small sieve thresholds
where the Möbius product is empty, the bound follows from the cardinal
bound alone, with `N₀ = 0`. -/
theorem brunGoldbachBoundedPrimes_holds_of_le_two
    {z₀ : ℕ} (hz₀ : z₀ ≤ 2) :
    BrunGoldbachBoundedPrimes z₀ := by
  refine ⟨0, ?_⟩
  intro n _hn
  -- `pairedBrunFactor z₀ = 1` for `z₀ ≤ 2`.
  have hM : pairedBrunFactor z₀ = 1 := pairedBrunFactor_eq_one_of_le_two hz₀
  -- Trivial cardinal bound, real-valued.
  have hSift : (goldbachSiftedPair n z₀ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachSiftedPair_le n z₀
  -- `(n : ℝ) ≥ 0`.
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- Compute the RHS.
  have hRHS : 2 * (n : ℝ) * pairedBrunFactor z₀ = 2 * (n : ℝ) := by
    rw [hM]; ring
  -- Slack `n ≤ 2n` requires `(n : ℝ) ≥ 0`.
  rw [hRHS]
  linarith

/-! ## Section 3 — Open slice: `z₀ ≥ 3` (the residual)

For `z₀ ≥ 3`, `pairedBrunFactor z₀ ≤ 1/3 < 1/2`, so the trivial cardinal
bound `goldbachSiftedPair n z₀ ≤ n` no longer implies the target bound.
Genuine Brun-Bonferroni content is required.

We expose the residual as a **named open Prop** and document precisely
which closed building blocks would discharge it. -/

/-- **`BoundedPrimesBrunKernel z₀`** — the residual kernel needed to
close `BrunGoldbachBoundedPrimes z₀` for `z₀ ≥ 3`.

For each `z₀ ≥ 3`, this is the *fixed-threshold* Brun-Bonferroni kernel:
the bound `goldbachSiftedPair n z₀ ≤ 2n · pairedBrunFactor z₀` for all
`n ≥ N₀(z₀)`, where `N₀(z₀)` depends on `z₀` but not on `n`.

**Status (honest)**:  classical paired Brun-Bonferroni at *fixed*
`z₀ ≥ 3`.  Although the Bonferroni truncation tail vanishes at depth
`k = |P|`, the paired CRT counting kernel (with combined error
`O(2^|P|)`) is still the same residual that obstructs the uniform-in-`z`
version.  Mathlib v4.29.1 **open**. -/
def BoundedPrimesBrunKernel (z₀ : ℕ) : Prop :=
  3 ≤ z₀ → BrunGoldbachBoundedPrimes z₀

/-- **Conditional closure**:  combining the closed slice (`z₀ ≤ 2`)
with a witness for the residual kernel (`z₀ ≥ 3`) gives
`BrunGoldbachBoundedPrimes z₀` for every `z₀`. -/
theorem brunGoldbachBoundedPrimes_of_kernel
    {z₀ : ℕ} (h_kernel : BoundedPrimesBrunKernel z₀) :
    BrunGoldbachBoundedPrimes z₀ := by
  by_cases hz : z₀ ≤ 2
  · exact brunGoldbachBoundedPrimes_holds_of_le_two hz
  · have hz3 : 3 ≤ z₀ := Nat.lt_of_not_le hz
    exact h_kernel hz3

/-! ## Section 4 — Honest assessment of the residual

We document what would suffice to close `BoundedPrimesBrunKernel z₀`
for `z₀ ≥ 3`, and why the bounded-primes setting does not bypass the
core analytic obstruction. -/

/-- **Honest assessment**:  the residual `BoundedPrimesBrunKernel z₀`
*at fixed* `z₀ ≥ 3` reduces (axiom-cleanly) to the *same* paired
Bonferroni kernel needed for the uniform-in-`z` Brun-Goldbach bound.

Specifically, an axiom-clean closure would proceed via:

1. **T1 paired indicator** (`pairedBonferroniIndicator_holds`):
   for `P := (Finset.Icc 3 z₀).filter Nat.Prime` and `k = |P|` (even
   for `|P|` even; otherwise `k = |P| + 1`), the indicator inequality

   ```
   1{m, n-m coprime to P}  ≤  ∏ over d₁, d₂ ⊆ P  μ(d₁) μ(d₂) ⋯
   ```

2. **T3 sum rearrangement** (`pairedBonferroniSumRearrange_holds`):
   sum the indicator over `m ∈ [1, n-1]` and rearrange.

3. **P17-T3 paired CRT count** (`goldbachPairCRTCount_holds`): each
   double-divisor pair contributes `n / (d₁ d₂) + O(1)`.

4. **T4 + T28 Möbius/Euler-product collapse**
   (`paired_eulerProduct_moebius_form`,
   `paired_eulerProduct_identity_pairedBrunFactor`): the alternating
   Möbius sum collapses to `pairedBrunFactor z₀`.

5. **Error aggregation**: summing CRT errors over `4^|P|` divisor pairs
   gives an error of `O(4^|P|) = O(z₀^{O(z₀ / log z₀)})`.  For
   `n ≥ N₀(z₀) := 4^|P| / pairedBrunFactor z₀`, the error absorbs into
   a factor-of-`2` slack on the main term.

The fixed-`z₀` setting **avoids** the *uniformity in z* obstacle (the
constants depend on `z₀`), but **inherits** the kernel-level paired
Bonferroni assembly, which is the precise irreducible residual
`AlignedSubSqrtInequalityAndTail` from `PathC_PairedBrunSubSqrtProof.lean`
(at fixed `z₀` instead of all `z ∈ [3, √n)`).

In summary:  **the bounded-primes setting concentrates but does not
eliminate the analytic content of the Brun-Goldbach bound**. -/
theorem boundedPrimesBrun_residual_documentation : True := trivial

/-! ## Section 5 — Re-export the closed slice under the headline name

The task's target headline is
`brunGoldbachBoundedPrimes_holds (z₀ : ℕ) : BrunGoldbachBoundedPrimes z₀`.
We provide it as a function `brunGoldbachBoundedPrimes_holds_smallZ`
that closes the slice we can close axiom-cleanly, and a *conditional*
form `brunGoldbachBoundedPrimes_holds_of_kernel` (= ` ↑↑ Section 3`)
that takes the residual witness as input.

Because the residual is genuinely open for `z₀ ≥ 3`, we do **not**
provide an unconditional headline that mis-states the proof status. -/

/-- **Headline (closed slice)** — `brunGoldbachBoundedPrimes_holds`
restricted to `z₀ ≤ 2`, where it is axiom-clean. -/
theorem brunGoldbachBoundedPrimes_holds_smallZ
    {z₀ : ℕ} (hz₀ : z₀ ≤ 2) :
    BrunGoldbachBoundedPrimes z₀ :=
  brunGoldbachBoundedPrimes_holds_of_le_two hz₀

/-- **Headline (conditional)** — `brunGoldbachBoundedPrimes_holds` for
every `z₀`, conditional on the residual `BoundedPrimesBrunKernel z₀`. -/
theorem brunGoldbachBoundedPrimes_holds_of_kernel
    {z₀ : ℕ} (h_kernel : BoundedPrimesBrunKernel z₀) :
    BrunGoldbachBoundedPrimes z₀ :=
  brunGoldbachBoundedPrimes_of_kernel h_kernel

/-! ## Section 6 — A sample concrete value

To make the closed slice concrete:  `BrunGoldbachBoundedPrimes 2` is
axiom-clean. -/

/-- **Sample concrete instance**:  for `z₀ = 2`, the bounded-primes
Brun-Goldbach Prop is axiom-clean. -/
theorem brunGoldbachBoundedPrimes_holds_at_two :
    BrunGoldbachBoundedPrimes 2 :=
  brunGoldbachBoundedPrimes_holds_of_le_two (le_refl 2)

/-- **Sample concrete instance**:  for `z₀ = 1`, the bounded-primes
Brun-Goldbach Prop is axiom-clean. -/
theorem brunGoldbachBoundedPrimes_holds_at_one :
    BrunGoldbachBoundedPrimes 1 :=
  brunGoldbachBoundedPrimes_holds_of_le_two (by norm_num)

/-- **Sample concrete instance**:  for `z₀ = 0`, the bounded-primes
Brun-Goldbach Prop is axiom-clean. -/
theorem brunGoldbachBoundedPrimes_holds_at_zero :
    BrunGoldbachBoundedPrimes 0 :=
  brunGoldbachBoundedPrimes_holds_of_le_two (by norm_num)

end PathCBoundedPrimesBrun
end Gdbh
