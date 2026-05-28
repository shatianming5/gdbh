/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T10 (Phase 19 / Path C — Constant alignment between the
paired Brun-Bonferroni indicator (P19-T1) and the AtSqrt / SubSqrt
"aligned inequality + tail" residuals (P18-T4 / P18-T5)).
-/
import Gdbh.PathC_PairedBonferroniIndicator
import Gdbh.PathC_PairedBrunGoldbachAtSqrt
import Gdbh.PathC_PairedBrunSubSqrtProof

/-!
# Path C — P19-T10: Paired Bonferroni constant alignment (C₂ ≤ 2)

P18-T4 (AtSqrt) and P18-T5 (SubSqrt) expose the residuals
`PairedBonferroniInequalityAtSqrtAlignedWithTail` /
`PairedBonferroniInequalitySubSqrtAlignedWithTail`, both of which
demand `0 < C₂ ∧ C₂ ≤ 2`.  The bound `C₂ ≤ 2` is the **alignment
constraint** with T5-Sqrt's tail constant `C₃ = 2` (established in
`pairedBonferroniTailAtSqrt_holds` / `pairedBonferroniTailSubSqrt_holds`).

P19-T1 just closed the *indicator-level* paired Brun-Bonferroni
inequality `PairedBonferroniIndicator`:

```
   1{m, n - m both coprime to P}
     ≤ (∑_{d₁ ⊆ P, |d₁| ≤ k} μ(d₁.prod id) · 1{d₁.prod id ∣ m})
       · (∑_{d₂ ⊆ P, |d₂| ≤ k} μ(d₂.prod id) · 1{d₂.prod id ∣ (n - m)})  .
```

This file tracks the constant in the assembly from the indicator
inequality to the AtSqrt / SubSqrt aligned residual and shows the
alignment is **automatic** (natural `C₂ = 1` satisfies `C₂ ≤ 2`).

## Mathematical content

The indicator-level inequality from P19-T1 has **no explicit constant**:
the multiplicative bound `1 ≤ S₁ · S₂` carries an implicit factor of 1.

After summing over `m ∈ [1, n - 1]`, applying T3 (CRT counting), T4
(paired Euler product identity), and T5-Sqrt (Stirling tail), the
natural Bonferroni assembly delivers a bound

```
   goldbachSiftedPair n z  ≤  1 · n · pairedBrunFactor z
                              +  1 · n · π(z)^{2k+1}/(2k+1)! ,
```

i.e. with **`C₂ = 1`** in front of *both* the main term and the
truncation tail.  Since `0 < 1 ≤ 2`, the alignment constraint
`C₂ ≤ 2` of the AtSqrt / SubSqrt aligned residuals is satisfied
**automatically**.

## Deliverables

* `pairedBonferroniIndicator_constant_one` — bookkeeping lemma noting
  the indicator-level Prop carries an implicit `C₂ = 1`.

* `PairedBonferroniNaturalAtSqrt` / `PairedBonferroniNaturalSubSqrt` —
  the **reduced residual** Props with explicit `C₂ = 1`.

* `pairedBonferroniInequalityAtSqrtAlignedWithTail_of_natural` /
  `pairedBonferroniInequalitySubSqrtAlignedWithTail_of_natural` —
  **bridge theorems** showing the natural assembly implies the
  aligned residual with the alignment constraint `C₂ ≤ 2`
  **automatically satisfied** (via `C₂ = 1`).

* `PairedBonferroniNaturalAtSqrtWithTail` /
  `PairedBonferroniNaturalSubSqrtWithTail` — the **joint** form
  packaging the natural assembly with the closed tail bound at a
  shared witness `k`.

* `alignedInequalityAndTail_of_natural_with_tail` /
  `alignedSubSqrtInequalityAndTail_of_natural_with_tail` — **joint
  bridge** theorems delivering `AlignedInequalityAndTail` /
  `AlignedSubSqrtInequalityAndTail` directly with `C₂ = 1`,
  `C₃ = 2`.

## Verdict on the C₂ ≤ 2 question

The natural assembly delivers **C₂ = 1**, which trivially satisfies
`C₂ ≤ 2`.  The alignment is automatic; no refinement is needed.
The constant `C₂ ≤ 2` margin in the aligned residual is generous —
it accommodates assemblies that pick up a multiplicative factor up to
2 from any auxiliary slack.

## Axiom budget

Every theorem below is axiom-clean:  only `Classical.choice`,
`Quot.sound`, and `propext` are transitively used.  No `sorry`,
`axiom`, or `admit` appears.
-/

namespace Gdbh
namespace PathCPairedBonferroniConstantAlign

open Real
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPairSet goldbachSiftedPair_le
   mem_goldbachSiftedPairSet)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunRefinedComposition
  (refinedReservoir refinedReservoir_def)
open Gdbh.PathCPairedBrunSmallZ
  (pairedBrunFactor_eq_one_of_le_two refinedReservoir_nonneg)
open Gdbh.PathCPairedBrunGoldbachAtSqrt
  (PairedBonferroniInequalityAtSqrtAlignedWithTail
   PairedBonferroniTailAtSqrt
   pairedBonferroniTailAtSqrt_holds
   AlignedInequalityAndTail)
open Gdbh.PathCPairedBrunSubSqrtProof
  (PairedBonferroniInequalitySubSqrtAlignedWithTail
   PairedBonferroniTailSubSqrt
   pairedBonferroniTailSubSqrt_holds
   AlignedSubSqrtInequalityAndTail)

/-! ## Section 1 — The indicator Prop carries no explicit constant

`PairedBonferroniIndicator` (P19-T1) is stated without any explicit
constant on the right-hand side.  The bound is

```
   1{m, n - m both coprime to P}
     ≤ S₁(m) · S₂(n - m) ,
```

where `S₁`, `S₂` are the truncated Möbius sums.  Multiplicatively,
this is a *factor-of-1* bound:  the implicit `C₂` is exactly `1`.

We expose this observation by deriving a trivial restatement that
**makes the constant explicit**.

Note:  this is purely a *bookkeeping* lemma.  The content is the
P19-T1 closure; we merely record that the right-hand side carries
no hidden multiplicative factor. -/

/-- The natural multiplicative constant in the indicator-level paired
Bonferroni inequality is `1`.

This is a trivial restatement of `PairedBonferroniIndicator` with a
unit factor `1 *` inserted on the right-hand side, making the natural
constant explicit. -/
theorem pairedBonferroniIndicator_constant_one
    (h : Gdbh.PathCPairedBonferroniIndicator.PairedBonferroniIndicator) :
    ∀ (P : Finset ℕ) (m n : ℕ) (k : ℕ),
      (∀ p ∈ P, Nat.Prime p) →
      Even k →
      m ≤ n →
      (if (∀ p ∈ P, ¬ p ∣ m) ∧ (∀ p ∈ P, ¬ p ∣ (n - m)) then (1 : ℝ) else 0)
        ≤ (1 : ℝ) *
          ((∑ d₁ ∈ P.powerset.filter (fun d => d.card ≤ k),
             (ArithmeticFunction.moebius (d₁.prod id) : ℝ) *
               (if (d₁.prod id) ∣ m then (1 : ℝ) else 0))
          * (∑ d₂ ∈ P.powerset.filter (fun d => d.card ≤ k),
               (ArithmeticFunction.moebius (d₂.prod id) : ℝ) *
                 (if (d₂.prod id) ∣ (n - m) then (1 : ℝ) else 0))) := by
  intro P m n k hP hk hmn
  have hbase := h P m n k hP hk hmn
  -- Replace the RHS `S₁ * S₂` with `1 * (S₁ * S₂)`.
  simpa [one_mul] using hbase

/-! ## Section 2 — Natural Bonferroni assembly at sqrt (C₂ = 1)

We expose the **natural** Bonferroni assembly at the AtSqrt threshold:
the inequality

```
   goldbachSiftedPair n √n
     ≤ n · pairedBrunFactor √n
       + n · π(√n)^{2k+1}/(2k+1)! ,
```

i.e. with an *explicit* leading constant `1`.

This is the residual Prop that *would* be delivered by combining
T3 (paired CRT counting), T4 (paired Euler product), the indicator
sum rearrangement, and T5-Sqrt.  Its closure is the genuine analytic
content of P18-T4. -/

/-- **`PairedBonferroniNaturalAtSqrt`** — the natural large-`n`
Bonferroni assembly at the AtSqrt threshold with explicit leading
constant `1`.

```
∃ N₁, ∃ k : ℕ → ℕ, 4 ≤ N₁ ∧ ∀ n ≥ N₁,
  goldbachSiftedPair n √n
    ≤ n · pairedBrunFactor √n
      + n · π(√n)^{2 k(n) + 1} / (2 k(n) + 1)! .
```

The constant `C₂ = 1` is **natural**:  it arises directly from the
multiplicative indicator bound `1 ≤ S₁ · S₂` (no auxiliary factor). -/
def PairedBonferroniNaturalAtSqrt : Prop :=
  ∃ N₁ : ℕ, ∃ k : ℕ → ℕ,
    4 ≤ N₁ ∧
    ∀ n : ℕ, N₁ ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ)
              * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
              / ((2 * k n + 1).factorial : ℝ)

/-! ## Section 3 — Bridge: natural assembly ⇒ aligned residual (AtSqrt)

The natural constant `C₂ = 1` satisfies `0 < 1 ≤ 2`, so the alignment
constraint of `PairedBonferroniInequalityAtSqrtAlignedWithTail` is
automatic. -/

/-- **Bridge** (AtSqrt): the natural assembly with `C₂ = 1` implies the
aligned-with-tail residual with `C₂ = 1 ≤ 2`. -/
theorem pairedBonferroniInequalityAtSqrtAlignedWithTail_of_natural
    (h : PairedBonferroniNaturalAtSqrt) :
    PairedBonferroniInequalityAtSqrtAlignedWithTail := by
  obtain ⟨N₁, k, hN, hIneq⟩ := h
  refine ⟨1, N₁, k, by norm_num, by norm_num, hN, ?_⟩
  intro n hn
  have hbase := hIneq n hn
  -- Rewrite the RHS to match the aligned-form `C₂ * n * factor + C₂ * n * tail`
  -- with `C₂ = 1`.
  have hRHS_eq :
      (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ)
              * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
              / ((2 * k n + 1).factorial : ℝ)
        = (1 : ℝ) * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + (1 : ℝ) * (n : ℝ)
                * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ) := by
    ring
  rw [hRHS_eq] at hbase
  exact hbase

/-! ## Section 4 — Joint bridge: natural assembly ⇒ AlignedInequalityAndTail

Combining the natural assembly with the tail bound at the same shared
witness `k`, we obtain the **joint** witness Prop
`AlignedInequalityAndTail` directly. -/

/-- A **stronger** natural assembly Prop that includes the tail bound
at the *same* shared witness.  This is the form the standard
derivation actually produces:  the same `k` controls both the main
inequality and the tail. -/
def PairedBonferroniNaturalAtSqrtWithTail : Prop :=
  ∃ N : ℕ, ∃ k : ℕ → ℕ,
    4 ≤ N ∧
    (∀ n : ℕ, N ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ)
              * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
              / ((2 * k n + 1).factorial : ℝ)) ∧
    (∀ n : ℕ, N ≤ n →
      2 * (n : ℝ)
          * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
          / ((2 * k n + 1).factorial : ℝ)
        ≤ refinedReservoir n (Nat.sqrt n))

/-- **Joint bridge** (AtSqrt): the natural assembly with tail at the
same witness `k` implies the joint `AlignedInequalityAndTail` with
`C₂ = 1` and `C₃ = 2`. -/
theorem alignedInequalityAndTail_of_natural_with_tail
    (h : PairedBonferroniNaturalAtSqrtWithTail) :
    AlignedInequalityAndTail := by
  obtain ⟨N, k, hN, hIneq, hTail⟩ := h
  refine ⟨1, 2, N, k, by norm_num, by norm_num, by norm_num, hN, ?_, ?_⟩
  · -- Main inequality with `C₂ = 1`.
    intro n hn
    have hbase := hIneq n hn
    have hRHS_eq :
        (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + (n : ℝ)
                * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ)
          = (1 : ℝ) * (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
              + (1 : ℝ) * (n : ℝ)
                  * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * k n + 1)
                  / ((2 * k n + 1).factorial : ℝ) := by
      ring
    rw [hRHS_eq] at hbase
    exact hbase
  · -- Tail bound with `C₃ = 2`.
    intro n hn
    exact hTail n hn

/-! ## Section 5 — Natural Bonferroni assembly at sub-sqrt (C₂ = 1)

Parallel development for the SubSqrt residual. -/

/-- **`PairedBonferroniNaturalSubSqrt`** — the natural large-`n`
Bonferroni assembly at sub-`√n` thresholds with explicit leading
constant `1`.

```
∃ N₁, ∃ k : ℕ → ℕ, 10 ≤ N₁ ∧ ∀ n ≥ N₁, ∀ z ∈ [3, √n),
  goldbachSiftedPair n z
    ≤ n · pairedBrunFactor z
      + n · π(z)^{2 k(n) + 1} / (2 k(n) + 1)! .
```
-/
def PairedBonferroniNaturalSubSqrt : Prop :=
  ∃ N₁ : ℕ, ∃ k : ℕ → ℕ,
    10 ≤ N₁ ∧
    ∀ n z : ℕ, N₁ ≤ n → 3 ≤ z → z < Nat.sqrt n →
      (goldbachSiftedPair n z : ℝ)
        ≤ (n : ℝ) * pairedBrunFactor z
          + (n : ℝ)
              * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
              / ((2 * k n + 1).factorial : ℝ)

/-- **Bridge** (SubSqrt): the natural assembly with `C₂ = 1` implies
the aligned-with-tail residual with `C₂ = 1 ≤ 2`. -/
theorem pairedBonferroniInequalitySubSqrtAlignedWithTail_of_natural
    (h : PairedBonferroniNaturalSubSqrt) :
    PairedBonferroniInequalitySubSqrtAlignedWithTail := by
  obtain ⟨N₁, k, hN, hIneq⟩ := h
  refine ⟨1, N₁, k, by norm_num, by norm_num, hN, ?_⟩
  intro n z hn hz_ge_3 hz_lt_sqrt
  have hbase := hIneq n z hn hz_ge_3 hz_lt_sqrt
  have hRHS_eq :
      (n : ℝ) * pairedBrunFactor z
          + (n : ℝ)
              * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
              / ((2 * k n + 1).factorial : ℝ)
        = (1 : ℝ) * (n : ℝ) * pairedBrunFactor z
            + (1 : ℝ) * (n : ℝ)
                * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ) := by
    ring
  rw [hRHS_eq] at hbase
  exact hbase

/-- A **stronger** natural assembly Prop (SubSqrt form) that includes
the tail bound at the *same* shared witness. -/
def PairedBonferroniNaturalSubSqrtWithTail : Prop :=
  ∃ N : ℕ, ∃ k : ℕ → ℕ,
    10 ≤ N ∧
    (∀ n z : ℕ, N ≤ n → 3 ≤ z → z < Nat.sqrt n →
      (goldbachSiftedPair n z : ℝ)
        ≤ (n : ℝ) * pairedBrunFactor z
          + (n : ℝ)
              * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
              / ((2 * k n + 1).factorial : ℝ)) ∧
    (∀ n z : ℕ, N ≤ n → 3 ≤ z → z < Nat.sqrt n →
      2 * (n : ℝ)
          * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
          / ((2 * k n + 1).factorial : ℝ)
        ≤ refinedReservoir n z)

/-- **Joint bridge** (SubSqrt): the natural assembly with tail at the
same witness `k` implies the joint `AlignedSubSqrtInequalityAndTail`
with `C₂ = 1` and `C₃ = 2`. -/
theorem alignedSubSqrtInequalityAndTail_of_natural_with_tail
    (h : PairedBonferroniNaturalSubSqrtWithTail) :
    AlignedSubSqrtInequalityAndTail := by
  obtain ⟨N, k, hN, hIneq, hTail⟩ := h
  refine ⟨1, 2, N, k, by norm_num, by norm_num, by norm_num, hN, ?_, ?_⟩
  · intro n z hn hz_ge_3 hz_lt_sqrt
    have hbase := hIneq n z hn hz_ge_3 hz_lt_sqrt
    have hRHS_eq :
        (n : ℝ) * pairedBrunFactor z
            + (n : ℝ)
                * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
                / ((2 * k n + 1).factorial : ℝ)
          = (1 : ℝ) * (n : ℝ) * pairedBrunFactor z
              + (1 : ℝ) * (n : ℝ)
                  * (Nat.primeCounting z : ℝ)^(2 * k n + 1)
                  / ((2 * k n + 1).factorial : ℝ) := by
      ring
    rw [hRHS_eq] at hbase
    exact hbase
  · intro n z hn hz_ge_3 hz_lt_sqrt
    exact hTail n z hn hz_ge_3 hz_lt_sqrt

/-! ## Section 6 — Strengthened bridges: weaker natural assembly with
the closed tail installed externally

For convenience, we provide bridge theorems that consume only the
**main** part of the natural assembly (without the tail), since the
tail is closed unconditionally for *some* witness `k` via T5-Sqrt.

The catch:  the natural assembly's `k` may not match the closed
tail's `k`.  We sidestep this by re-using the natural assembly's `k`
on both sides — which requires the consumer to align their derivation
to the T5-Sqrt-canonical `k = fun n => 2 * n`.

For now, we content ourselves with the same-witness bridges in
§4 and §5, which is the form the standard derivation actually
produces. -/

/-! ## Section 7 — Verdict and summary -/

/-- **Verdict** on `C₂ ≤ 2`: with the natural Bonferroni assembly,
the constant `C₂ = 1` satisfies `C₂ ≤ 2`, so the alignment is
**automatic**.

This theorem is a trivial restatement of the inequality `1 ≤ 2`,
recorded here for documentation purposes. -/
theorem natural_C2_satisfies_alignment : (1 : ℝ) ≤ 2 := by norm_num

/-- **Verdict** on `0 < C₂`: with the natural Bonferroni assembly,
`C₂ = 1 > 0`. -/
theorem natural_C2_positive : (0 : ℝ) < 1 := by norm_num

/-- **End-to-end verdict** combining both alignment constraints:
the natural constant `C₂ = 1` satisfies both `0 < C₂` and `C₂ ≤ 2`,
so any natural Bonferroni assembly with `C₂ = 1` slots directly into
the AtSqrt / SubSqrt aligned residuals. -/
theorem natural_C2_alignment_complete : (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 2 :=
  ⟨by norm_num, by norm_num⟩

/-! ## Section 8 — Summary

P19-T10 verifies that the **constant alignment** `C₂ ≤ 2` of the
aligned residuals `PairedBonferroniInequalityAtSqrtAlignedWithTail`
/ `PairedBonferroniInequalitySubSqrtAlignedWithTail` is **automatic**
under the natural Bonferroni assembly.

**Outcome**:

1. The indicator-level inequality from P19-T1
   (`PairedBonferroniIndicator`) has **no explicit constant** — it is
   a multiplicative bound `1 ≤ S₁ · S₂` with implicit factor 1.

2. The natural assembly Prop
   `PairedBonferroniNaturalAtSqrt` /
   `PairedBonferroniNaturalSubSqrt` codifies the inequality with
   **explicit `C₂ = 1`** in front of *both* the `pairedBrunFactor` and
   the truncation tail.

3. The bridge theorems
   `pairedBonferroniInequalityAtSqrtAlignedWithTail_of_natural` /
   `pairedBonferroniInequalitySubSqrtAlignedWithTail_of_natural`
   show: natural-`C₂ = 1` ⟹ aligned residual.  The alignment
   constraint `C₂ ≤ 2` is satisfied **automatically** by `1 ≤ 2`.

4. The joint bridge theorems
   `alignedInequalityAndTail_of_natural_with_tail` /
   `alignedSubSqrtInequalityAndTail_of_natural_with_tail`
   directly deliver the joint `AlignedInequalityAndTail` /
   `AlignedSubSqrtInequalityAndTail` from a natural assembly with the
   tail pre-installed at the same shared witness `k`.

**Honest residual after this file**:  the residual is the **natural
assembly** Props (`PairedBonferroniNaturalAtSqrt` /
`PairedBonferroniNaturalSubSqrt`), which require closing the
indicator → sum → main-term + tail chain via T3 (CRT) and T4
(Euler product) — these are still open as Phase 17 atoms whose
*concrete* outputs (not just statements) are required to close the
chain.  But the **constant** is no longer a residual: it is `1`,
which trivially satisfies the alignment constraint.

This task delivers no new analytic content; it is a **constant-tracking
audit** confirming that the constant constraint is already satisfied
by the natural derivation. -/

/-- **P19-T10 summary, in proof form.** -/
theorem pathC_p19_t10_summary : True := trivial

end PathCPairedBonferroniConstantAlign
end Gdbh
