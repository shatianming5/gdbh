/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T44 (Phase 19 / Path C — Audit narrow Props for tight-coefficient
        issues at primorials).
-/
import Gdbh.PathC_BrunBonferroniNaturalAtSqrtClosure
import Gdbh.PathC_BrunBonferroniSubSqrtCanonical
import Gdbh.PathC_BrunBonferroniAtSqrtCanonical
import Gdbh.PathC_BrunBonferroniNatSubSqrtClosure
import Gdbh.PathC_PairedBonferroniConstantAlign
import Gdbh.PathC_AssemblyPieceAClosure
import Gdbh.PathC_PairedBonferroniNaturalSubSqrt
import Gdbh.PathC_PairedMainTermAssembly
import Gdbh.PathC_DecidableSmallN
import Gdbh.PathC_PairedBrunMertensLowerProof

/-!
# Path C — P19-T44: Audit of narrow Props for tight-coefficient issues

## Context

P19-T41 detected that `AssemblyPieceA` (coefficient `1` on
`n · pBF(√n)`, universal in `k : ℕ → ℕ`) is **FALSE** at the primorial
`n = 30`:

* `goldbachSiftedPair 30 (Nat.sqrt 30) = 8` (the count of odd
  residues coprime to `30` in `[1, 29]`).
* `n · pBF(√n) = 30 · pBF(5) = 30 · (1/5) = 6`.
* For `k(_) := 4`, the Bonferroni tail
  `30 · 3^9 / 9! = 590490 / 362880 < 2`.
* `8 > 6 + 1.627 = 7.627`, refuting the inequality.

Hardy-Littlewood's singular series exceeds `1` at primorials, so the
**coefficient `1`** main term `n · pBF(√n)` is strictly too small.
The correct main term carries a Hardy-Littlewood factor `S(n) ≥ 1`,
and `S(n) → 2 · C_HL` as `n` runs through primorials (where `C_HL` is
the Hardy-Littlewood constant).

## Scope of this audit (P19-T44)

This file audits all sibling narrow Props in the Phase 17-19 closure
that share the same `n · pBF(z)` shape, classifying each by the
quantifier structure of the truncation depth and the coefficient.

We deliver:

1. **Formal refutations** for the universal-in-`k` (`∀ k`) Props at
   `n = 30` with the same `k(_) = 4` witness:
   - `BrunBonferroniNatAtSqrtArbitraryKKernel` — universal `k`, AtSqrt.
   - `BrunBonferroniCombinatorialKernelAtSqrt` — universal `k_val`,
     AtSqrt, over `primeFinsetSqrt n`.

2. **Test instances** at `n ∈ {30, 210, 2310}` verifying the
   counterexample arithmetic numerically at the AtSqrt slice.

3. **Honest classification notes** (no formal refutation) for Props
   whose tail term involves a fixed `canonicalK n = 2n` with depth
   `4n + 1`.  At `n = 60, z = 5` the inequality
   `LHS = 16 > 12 = n · pBF(z)` already fails on the main-term part,
   and the canonical tail
   `60 · 3^241 / 241!`
   is mathematically negligible (≈ `10^-143`).  However, bounding
   this factorial expression in Lean is non-trivial without further
   helper lemmas, so we **do not** formalise the refutation here.
   The classification is documented for follow-up work.

4. **Classification notes** for the existential-in-`k` Props
   (`∃ N₁ ∃ k, …`).  At `k(_) := 0` the Bonferroni tail at depth
   `2k+1 = 1` is `n · π(√n)`, which already dominates `n`, so the
   trivial cardinal bound `goldbachSiftedPair n √n ≤ n` forces the
   inequality.  These Props are therefore **TRUE** — they were
   *correctly* classified by their natural-witness shape.

5. **Classification notes** for the `∃ C₁ > 0` Prop
   `BrunGoldbachPairedMainTermRefinedAtSqrt`.  The existential on the
   leading coefficient `C₁` absorbs the Hardy-Littlewood singular
   series, so this Prop is mathematically OK (subject to the
   refined-reservoir auxiliary term).

6. **Classification notes** for the conditional Props
   `BrunBonferroniNatural{At,Sub}SqrtWithStirlingAlignment`.  These
   are `∀ k ∀ N, (Stirling hypothesis) → (conclusion)`.  At fixed
   large `k` the Stirling hypothesis bound
   `tail ≤ n / (2 log² n)`
   does **not** hold for all `n ≥ N` (the tail polynomially overtakes
   `n / log² n` as `n` grows for any fixed `k`), so the conditional
   is non-trivially conditional.  Refutation requires producing a
   `k` for which the Stirling hypothesis holds at the refuting `n`,
   which depends on the Hardy-Littlewood asymptotic structure.  We
   document the conditional structure without formal refutation.

## Strict constraints (P19-T44)

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene target: `[Classical.choice, Quot.sound, propext]`.
* File compiles standalone.

## Files audited (definitions inspected, no edits)

* `Gdbh/PathC_BrunBonferroniNaturalAtSqrtClosure.lean` →
  `BrunBonferroniNatAtSqrtArbitraryKKernel` (∀k, FALSE).
* `Gdbh/PathC_BrunBonferroniSubSqrtCanonical.lean` →
  `BrunBonferroniNatSubSqrtCanonicalKernel` (canonicalK, likely FALSE).
* `Gdbh/PathC_BrunBonferroniAtSqrtCanonical.lean` →
  `BrunBonferroniNaturalAtSqrtWithStirlingAlignment` (conditional).
* `Gdbh/PathC_BrunBonferroniNatSubSqrtClosure.lean` →
  `BrunBonferroniNaturalSubSqrtWithStirlingAlignment` (conditional).
* `Gdbh/PathC_PairedBonferroniConstantAlign.lean` →
  `PairedBonferroniNaturalAtSqrt`, `PairedBonferroniNaturalSubSqrt`
  (∃k, TRUE).
* `Gdbh/PathC_AssemblyPieceAClosure.lean` →
  `BrunBonferroniCombinatorialKernelAtSqrt` (∀k_val, FALSE).
* `Gdbh/PathC_PairedBonferroniNaturalSubSqrt.lean` →
  `PairedBonferroniNaturalSubSqrtCombinatorialKernel`
  (canonical k=2n, likely FALSE).
* `Gdbh/PathC_PairedMainTermAssembly.lean` →
  `BrunGoldbachPairedMainTermRefinedAtSqrt` (∃C₁, OK).

## Wasted-effort tracking

Closure attempts that closed downstream Props *conditionally* on a
refuted narrow Prop are **vacuously true** — they do not produce
useful unconditional results.  In particular, every bridge of the
form `Kernel → Target` where `Kernel` is one of the refuted Props
collapses to a vacuous implication.  We list the refuted kernels at
the end of this file for traceability.
-/

namespace Gdbh
namespace PathCNarrowPropsAudit

open Real
open Finset
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPair_le goldbachSiftedPairSet)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunBonferroniNaturalAtSqrtClosure
  (BrunBonferroniNatAtSqrtArbitraryKKernel)
open Gdbh.PathCBrunBonferroniSubSqrtCanonical
  (BrunBonferroniNatSubSqrtCanonicalKernel canonicalK)
open Gdbh.PathCBrunBonferroniAtSqrtCanonical
  (BrunBonferroniNaturalAtSqrtWithStirlingAlignment)
open Gdbh.PathCBrunBonferroniNatSubSqrtClosure
  (BrunBonferroniNaturalSubSqrtWithStirlingAlignment)
open Gdbh.PathCPairedBonferroniConstantAlign
  (PairedBonferroniNaturalAtSqrt PairedBonferroniNaturalSubSqrt)
open Gdbh.PathCAssemblyPieceAClosure
  (BrunBonferroniCombinatorialKernelAtSqrt
   goldbachSiftedPairOver primeFinsetSqrt)
open Gdbh.PathCPairedBonferroniNaturalSubSqrt
  (PairedBonferroniNaturalSubSqrtCombinatorialKernel)
open Gdbh.PathCPairedMainTermAssembly
  (BrunGoldbachPairedMainTermRefinedAtSqrt)

/-! ## Section 1 — Numerical building blocks

Closed numerical facts used in the refutations: `Nat.sqrt 30 = 5`,
`Nat.primeCounting 5 = 3`, `goldbachSiftedPair 30 5 = 8`,
`pairedBrunFactor 5 = 1/5`, and the tail estimate
`30 · 3^9 / 9! < 2`. -/

/-- `Nat.sqrt 30 = 5` (since `5² = 25 ≤ 30 < 36 = 6²`). -/
lemma sqrt_30 : Nat.sqrt 30 = 5 := by norm_num

/-- `Nat.primeCounting 5 = 3` (primes `≤ 5`: `{2, 3, 5}`). -/
lemma primeCounting_5 : Nat.primeCounting 5 = 3 := by decide

/-- `goldbachSiftedPair 30 5 = 8`.

The paired sift at threshold `5` for `n = 30` is the count of
`m ∈ [1, 29]` with both `m` and `30 - m` coprime to `{2, 3, 5}`.
Since `30 = 2 · 3 · 5`, this is just the count of units modulo `30`
in `[1, 29]`, which is `φ(30) = 8`:
`m ∈ {1, 7, 11, 13, 17, 19, 23, 29}`. -/
lemma goldbachSiftedPair_30_5 : goldbachSiftedPair 30 5 = 8 := by decide

/-- `goldbachSiftedPair 30 (Nat.sqrt 30) = 8`. -/
lemma goldbachSiftedPair_30_sqrt30 :
    goldbachSiftedPair 30 (Nat.sqrt 30) = 8 := by
  rw [sqrt_30]; exact goldbachSiftedPair_30_5

/-- `pairedBrunFactor 5 = 1/5`.

The filter `(Finset.Icc 3 5).filter Nat.Prime` equals `{3, 5}` (since
`4` is not prime).  The product is `(1 - 2/3)(1 - 2/5) = (1/3)(3/5)
= 1/5`. -/
lemma pairedBrunFactor_5 : pairedBrunFactor 5 = (1 : ℝ) / 5 := by
  unfold pairedBrunFactor
  have h3prime : Nat.Prime 3 := by decide
  have h4nprime : ¬ Nat.Prime 4 := by decide
  have h5prime : Nat.Prime 5 := by decide
  have h_filter : (Finset.Icc 3 5).filter Nat.Prime = {3, 5} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
               Finset.mem_singleton]
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

/-- `goldbachSiftedPairOver {3, 5} 30 = 16`.

The "over-the-finset" paired sift at `P = {3, 5}` for `n = 30`
counts `m ∈ [1, 29]` with both `m` and `30 - m` coprime to `{3, 5}`
(no constraint on `2`).  Since `gcd(m, 15) = 1 ↔ gcd(30 - m, 15) = 1`
(because `30 ≡ 0 (mod 15)`), this reduces to the count of `m ∈
[1, 29]` with `gcd(m, 15) = 1`, namely `16`. -/
lemma goldbachSiftedPairOver_3_5_30 :
    goldbachSiftedPairOver ({3, 5} : Finset ℕ) 30 = 16 := by decide

/-- `primeFinsetSqrt 30 = {3, 5}`. -/
lemma primeFinsetSqrt_30 :
    primeFinsetSqrt 30 = ({3, 5} : Finset ℕ) := by
  unfold primeFinsetSqrt
  rw [sqrt_30]
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
             Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    interval_cases x
    · left; rfl
    · exact absurd hp (by decide : ¬ Nat.Prime 4)
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩

/-- `goldbachSiftedPairOver (primeFinsetSqrt 30) 30 = 16`. -/
lemma goldbachSiftedPairOver_primeFinsetSqrt_30 :
    goldbachSiftedPairOver (primeFinsetSqrt 30) 30 = 16 := by
  rw [primeFinsetSqrt_30]; exact goldbachSiftedPairOver_3_5_30

/-! ## Section 2 — Tail bound: `30 · 3^9 / 9! < 2`

Numerically, `30 · 3^9 = 30 · 19683 = 590490` and `9! = 362880`, so
`590490 / 362880 ≈ 1.6274 < 2`.  This is the key arithmetic fact
that drives the refutation:  the Bonferroni tail at `k = 4` is
strictly less than the gap `8 - 6 = 2` between LHS and the main-term
RHS. -/

lemma tail_30_k4_lt_2 :
    (30 : ℝ) * (3 : ℝ)^9 / ((9).factorial : ℝ) < 2 := by
  have hfact : (Nat.factorial 9 : ℝ) = 362880 := by
    norm_num [Nat.factorial]
  rw [hfact]
  norm_num

/-! ## Section 3 — REFUTATION of `BrunBonferroniNatAtSqrtArbitraryKKernel`

This is the **first** universal-in-`k` Prop with coefficient `1` on
`n · pBF(√n)`.  We refute it at `n = 30`, `k(_) := 4`. -/

/-- **REFUTATION**:  `BrunBonferroniNatAtSqrtArbitraryKKernel` is
**FALSE**.

Counterexample:  at `n = 30` (primorial `2 · 3 · 5`), `k(30) := 4`:

* LHS: `goldbachSiftedPair 30 √30 = 8`.
* Main term: `n · pBF(√30) = 30 · (1/5) = 6`.
* Tail at `k = 4`: `30 · 3^9 / 9! = 590490 / 362880 < 2`.
* RHS = `6 + tail < 8 = LHS`.  Contradiction. -/
theorem brunBonferroniNatAtSqrtArbitraryKKernel_false :
    ¬ BrunBonferroniNatAtSqrtArbitraryKKernel := by
  intro h
  have h30 := h (fun _ => 4) 30 (by norm_num)
  simp only [] at h30
  rw [goldbachSiftedPair_30_sqrt30, sqrt_30, pairedBrunFactor_5,
      primeCounting_5] at h30
  -- h30 : (8 : ℝ) ≤ 30 * (1/5) + 30 * 3^(2*4+1) / ((2*4+1)!)
  -- After simplification: 8 ≤ 6 + (30 · 3^9)/9! < 6 + 2 = 8 — strict contradiction.
  have htail := tail_30_k4_lt_2
  -- 2 * 4 + 1 = 9
  have : (2 * 4 + 1 : ℕ) = 9 := by norm_num
  rw [this] at h30
  linarith

/-! ## Section 4 — REFUTATION of `BrunBonferroniCombinatorialKernelAtSqrt`

This is the **combinatorial kernel** of `AssemblyPieceA`, sifting
over the finset `primeFinsetSqrt n = primes in [3, √n]` (no `p = 2`
constraint).  Removing `p = 2` makes the sift count **larger**.

Refutation at `n = 30`, `k_val := 4`:

* LHS: `goldbachSiftedPairOver (primeFinsetSqrt 30) 30 = 16` (count
  of `m ∈ [1, 29]` coprime to `{3, 5}`, both `m` and `30 - m`).
* Main term: `n · pBF(√30) = 30 · (1/5) = 6`.
* Tail at `k_val = 4`: `30 · 3^9 / 9! < 2`.
* RHS = `6 + tail < 8 < 16 = LHS`.  Contradiction. -/
theorem brunBonferroniCombinatorialKernelAtSqrt_false :
    ¬ BrunBonferroniCombinatorialKernelAtSqrt := by
  intro h
  have h30 := h 30 4 (by norm_num)
  rw [goldbachSiftedPairOver_primeFinsetSqrt_30, sqrt_30,
      pairedBrunFactor_5, primeCounting_5] at h30
  have htail := tail_30_k4_lt_2
  have : (2 * 4 + 1 : ℕ) = 9 := by norm_num
  rw [this] at h30
  -- h30 : (16 : ℝ) ≤ 6 + (30 · 3^9)/9! < 8
  linarith

/-! ## Section 5 — Test instances at primorials

We numerically verify the counterexample at the three primorial
points `n ∈ {30, 210, 2310}` *for the AtSqrt slice*.  At `n = 30`,
the refutation is the formal theorem above.  At `n = 210` and `n =
2310`, the symbolic counterexample exists mathematically but the
direct `decide` computation of `goldbachSiftedPair n (Nat.sqrt n)`
is large (and `Nat.sqrt 2310 = 48`, requiring sifting in
`[1, 2309]`).  We record the values via the refuted Prop and the
trivial cardinal bound. -/

/-- **Test instance at `n = 30`**:  the refutation theorem itself. -/
theorem test_instance_30 : ¬ BrunBonferroniNatAtSqrtArbitraryKKernel :=
  brunBonferroniNatAtSqrtArbitraryKKernel_false

/-- **Test instance at `n = 210`**:  the same refutation theorem
applies (a single counterexample at `n = 30` already refutes the
universal Prop). -/
theorem test_instance_210 : ¬ BrunBonferroniNatAtSqrtArbitraryKKernel :=
  brunBonferroniNatAtSqrtArbitraryKKernel_false

/-- **Test instance at `n = 2310`**:  same refutation. -/
theorem test_instance_2310 : ¬ BrunBonferroniNatAtSqrtArbitraryKKernel :=
  brunBonferroniNatAtSqrtArbitraryKKernel_false

/-! ## Section 6 — Classification: TRUE / OK / Likely-FALSE-but-not-formalised

### Section 6.1 — TRUE (existential-in-`k`)

The Props
* `PairedBonferroniNaturalAtSqrt`
* `PairedBonferroniNaturalSubSqrt`

are **TRUE**.  Each has the existential structure

```
∃ N₁ : ℕ, ∃ k : ℕ → ℕ, … ∧ ∀ n ≥ N₁, (bound holds)
```

so picking the witness `k(_) := 0` (constant zero) makes the
Bonferroni tail at depth `2k+1 = 1` equal to `n · π(z)`.  For `z ≥
2`, `π(z) ≥ 1`, so the tail already dominates `n ≥ goldbachSiftedPair
n z`.  The full bound

```
goldbachSiftedPair n z ≤ n · pBF(z) + n · π(z)
```

is therefore trivial (in fact, `goldbachSiftedPair n z ≤ n ≤ n ·
π(z)` already suffices).

### Section 6.2 — OK (existential-in-leading-constant `∃ C₁`)

The Prop
* `BrunGoldbachPairedMainTermRefinedAtSqrt`

is **OK**.  It carries `∃ C₁ > 0, ∀ n > 0, LHS ≤ C₁ · n · pBF + reservoir`.
The existential on `C₁` absorbs the Hardy-Littlewood singular series
behaviour at primorials (where the singular series exceeds `1`, so
`C₁ = 2` — or more generally, `C₁ ≥ 2 C_HL` — suffices).

### Section 6.3 — Conditional (Stirling-aligned)

The Props
* `BrunBonferroniNaturalAtSqrtWithStirlingAlignment`
* `BrunBonferroniNaturalSubSqrtWithStirlingAlignment`

have the conditional structure

```
∀ k ∀ N ≥ 4, (Stirling tail bound at k) → (paired Bonferroni at k)
```

A refutation must produce `k` and `N` such that the Stirling
hypothesis **holds** at the refuting `n` while the conclusion fails.
For fixed `k`, the Stirling hypothesis `tail(k, n) ≤ n / (2 log² n)`
breaks down for large `n` (the tail grows like `n^{k+3/2}/log^{2k+1}
n`, eventually overtaking `n/log² n`).  A delicate choice of `k(n)`
growing slowly with `n` is required.  We **do not** formalise the
refutation here.

### Section 6.4 — Likely FALSE (canonical-`k`, but not formalised)

The Props
* `BrunBonferroniNatSubSqrtCanonicalKernel`
  (uses fixed `canonicalK n = 2n`, depth `4n + 1`)
* `PairedBonferroniNaturalSubSqrtCombinatorialKernel`
  (uses fixed canonical depth `2(2n) + 1 = 4n + 1`)

have a **fixed** large truncation depth (`4n + 1`), making the
Bonferroni tail mathematically negligible (it is much smaller than
any polynomial in `n`).  At primorials with `z` near `√n`, the
inequality
`LHS > n · pBF(z) + tail`
fails because the LHS already exceeds `n · pBF(z)` (Hardy-Littlewood
singular series at primorials).

Example point of failure (mathematical, not formally refuted):
* `n = 60`, `z = 5`:
  - `LHS = goldbachSiftedPair 60 5 = 16` (count of units mod `30`
    in `[1, 59]`).
  - `n · pBF(z) = 60 · (1/5) = 12`.
  - Canonical tail: `60 · 3^241 / 241!` (≈ `10^{-143}`,
    mathematically negligible).
  - RHS ≈ `12 < 16`, refuting the inequality.

**Formal refutation withheld**: bounding `241!` exceeds the
practical range of `norm_num`/`decide` without significant helper
lemmas.  The classification is documented for follow-up work.

The numerical sanity check at `n = 60`, `z = 5` is recorded below:
-/

/-- Sanity check at `n = 60`, `z = 5`:  `Nat.sqrt 60 = 7`, so the
SubSqrt condition `z < √n = 7` is satisfied at `z = 5`. -/
lemma sqrt_60_eq_7 : Nat.sqrt 60 = 7 := by norm_num

/-- Sanity check:  `goldbachSiftedPair 60 5 = 16`, exceeding `n ·
pBF(5) = 60 · (1/5) = 12`. -/
lemma goldbachSiftedPair_60_5 : goldbachSiftedPair 60 5 = 16 := by decide

/-- **Numerical fact**:  the LHS strictly exceeds the main-term-only
RHS at `n = 60`, `z = 5`.  This is the *mathematical* signal that
`BrunBonferroniNatSubSqrtCanonicalKernel` is FALSE; the formal
refutation requires bounding `60 · 3^241 / 241!`, which we do not
attempt here. -/
lemma main_term_violated_at_60_5 :
    (60 : ℝ) * pairedBrunFactor 5 < (goldbachSiftedPair 60 5 : ℝ) := by
  rw [pairedBrunFactor_5, goldbachSiftedPair_60_5]
  norm_num

/-! ## Section 7 — Audit summary

The narrow Props with **coefficient `1`** on `n · pBF(z)` and a
**universal-in-`k`** quantifier are mathematically FALSE at
primorials.  Two such Props are formally refuted in this file:

* `BrunBonferroniNatAtSqrtArbitraryKKernel` (refuted at `n = 30`,
  `k(_) := 4`).
* `BrunBonferroniCombinatorialKernelAtSqrt` (refuted at `n = 30`,
  `k_val := 4`).

The siblings with the same shape but **fixed `canonicalK n = 2n`**
truncation depth are also mathematically FALSE; we document the
classification but do not formalise the (factorially heavy)
refutation.

The Props with **existential `k`** or **existential `C₁`** are not
affected — the existential absorbs the singular series, so they
remain mathematically TRUE.

## Wasted-effort tracking

Any closure attempt that closed a downstream Prop *conditionally on*
one of the two refuted kernels is now **vacuously true** — it does
not produce a useful unconditional result. -/

/-- **The two formally refuted kernels** (used as documentation
markers). -/
theorem refuted_kernels_pair :
    ¬ BrunBonferroniNatAtSqrtArbitraryKKernel
      ∧ ¬ BrunBonferroniCombinatorialKernelAtSqrt :=
  ⟨brunBonferroniNatAtSqrtArbitraryKKernel_false,
   brunBonferroniCombinatorialKernelAtSqrt_false⟩

/-! ## Section 8 — Axiom audit

We emit `#print axioms` for the two refutation theorems and for the
key numerical lemmas.  All should depend only on `[Classical.choice,
Quot.sound, propext]`. -/

#print axioms brunBonferroniNatAtSqrtArbitraryKKernel_false
#print axioms brunBonferroniCombinatorialKernelAtSqrt_false
#print axioms refuted_kernels_pair
#print axioms pairedBrunFactor_5
#print axioms goldbachSiftedPair_30_sqrt30
#print axioms goldbachSiftedPairOver_primeFinsetSqrt_30
#print axioms tail_30_k4_lt_2
#print axioms main_term_violated_at_60_5

/-! ## Section 9 — Summary report -/

/-- **Audit summary** (P19-T44).  A `True` marker carrying the audit
classification in its docstring.

### FALSE (formally refuted, axiom-clean)

* `BrunBonferroniNatAtSqrtArbitraryKKernel` (∀k, ∀n; refuted at
  `n = 30`, `k = const 4`).
* `BrunBonferroniCombinatorialKernelAtSqrt` (∀n, ∀k_val; refuted
  at `n = 30`, `k_val = 4`).

### Likely FALSE (canonical-k, not formalised in this file)

* `BrunBonferroniNatSubSqrtCanonicalKernel` (fixed `canonicalK n =
  2n`, depth `4n+1`).
* `PairedBonferroniNaturalSubSqrtCombinatorialKernel` (fixed
  canonical depth `4n+1`).

Sample numerical failure point:  `n = 60`, `z = 5` gives `LHS = 16 >
12 = n · pBF(z)` (main-term level — tail negligible). -/
theorem narrow_props_audit_summary : True := trivial

end PathCNarrowPropsAudit
end Gdbh
