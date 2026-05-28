/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T36 (Phase 19 / Path C — Master Brun-Bonferroni infrastructure
        file: a single re-export layer over the multi-file assembly chain).
-/
import Gdbh.PathC_ClassicalAssemblyChain
import Gdbh.PathC_AssemblyPieceAClosure
import Gdbh.PathC_FinsetAttachRoute
import Gdbh.PathC_BonferroniTailKernel
import Gdbh.PathC_MoebiusInversionRoute
import Gdbh.PathC_PairedMainTermAtSqrtReduction
import Gdbh.PathC_PairedMainTermFromLocalDensity
import Gdbh.PathC_PairedBonferroniIndicator
import Gdbh.PathC_PairedBonferroniSumRearrange
import Gdbh.PathC_GoldbachPairCRTCount

/-!
# Path C — P19-T36: Master Brun-Bonferroni infrastructure file

Single re-export layer over the multi-file Brun-Bonferroni assembly
chain produced across Phases 17-19.  Exposes one canonical name per
step under the `BrunMaster` namespace plus a single five-line composed
headline `assemblyPieceA_of_kernel_master`.  No new mathematical
content — every theorem is a direct re-export, with a comment
pointing at its source file/task.

## Namespace map (under `Gdbh.PathCBrunBonferroniMaster.BrunMaster`)

* Steps 1-7 of the classical chain ← P19-T32 (ClassicalAssemblyChain).
* Paired indicator / sum-rearrangement ← P19-T1 / P19-T3.
* CRT counting ← P17-T3 (GoldbachPairCRTCount).
* Disjoint-union Möbius density identity ← P19-T4.
* Paired Euler product identification (Brun factor & Möbius form)
  ← P17-T4 / P19-T28.
* Bonferroni truncation tail kernel & `(2/3)^|d|` bound ← P19-T19.
* Finset-attach factorisation ← P19-T30.
* Kernel → `AssemblyPieceA` bridge ← P19-T29.

## Headline

`assemblyPieceA_of_kernel_master :`
`  BrunBonferroniCombinatorialKernelAtSqrt → AssemblyPieceA`.

## Constraints

No `sorry`, no `axiom`, no `admit`.  Axiom hygiene
`[Classical.choice, Quot.sound, propext]`.  File compiles standalone.
Pure re-export.  P19-T36 deliverable.
-/

namespace Gdbh
namespace PathCBrunBonferroniMaster

/-! ## The `BrunMaster` namespace — one canonical name per building block. -/

namespace BrunMaster

/-! ### Section A — Step-by-step classical chain (P19-T32).

The seven classical Halberstam-Richert steps, each closed
individually in `Gdbh/PathC_ClassicalAssemblyChain.lean`. -/

/-- **Step 1 + 2** (combined): bound the paired sift count by the
double Möbius sum.  Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step1and2_siftCount_le_doubleSum :=
  @Gdbh.PathCClassicalAssemblyChain.step1and2_siftCount_le_doubleSum

/-- **Step 3**: disjoint / non-disjoint split of the double Möbius
sum.  Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step3_doubleSum_split :=
  @Gdbh.PathCClassicalAssemblyChain.step3_doubleSum_split

/-- **Step 4a**: untruncated disjoint double sum = single Möbius sum
by union folding.  Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step4a_disjoint_double_sum_eq_single_via_union :=
  @Gdbh.PathCClassicalAssemblyChain.step4a_disjoint_double_sum_eq_single_via_union

/-- **Step 4** disjoint-splits count: `2^|D|` ordered disjoint pairs
per `D`.  Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step4_disjoint_splits_count :=
  @Gdbh.PathCClassicalAssemblyChain.step4_disjoint_splits_count

/-- **Step 5a**: Euler product as Möbius signed sum.
Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step5a_eulerProduct_eq_moebius_sum :=
  @Gdbh.PathCClassicalAssemblyChain.step5a_eulerProduct_eq_moebius_sum

/-- **Step 5b**: Bonferroni truncation tail in `(2/3)^|d|` form.
Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step5b_bonferroni_truncation_tail :=
  @Gdbh.PathCClassicalAssemblyChain.step5b_bonferroni_truncation_tail

/-- **Step 6a**: `(P.powerset.filter (k < ·)).card ≤ P.powerset.card`.
Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step6a_tail_card_le_powerset_card :=
  @Gdbh.PathCClassicalAssemblyChain.step6a_tail_card_le_powerset_card

/-- **Step 6b**: each `(2/3)^|d| ≤ 1`.
Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step6b_two_thirds_pow_le_one :=
  @Gdbh.PathCClassicalAssemblyChain.step6b_two_thirds_pow_le_one

/-- **Step 6c**: tail sum bounded by the powerset cardinality.
Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step6c_tail_sum_le_card :=
  @Gdbh.PathCClassicalAssemblyChain.step6c_tail_sum_le_card

/-- **Step 7a**: bridge from the combinatorial kernel residual to
`AssemblyPieceA`.  Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step7a_assemblyPieceA_of_kernel :=
  @Gdbh.PathCClassicalAssemblyChain.step7a_assemblyPieceA_of_kernel

/-- **Step 7b**: conditional headline `kernel → AssemblyPieceA`.
Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev step7b_assemblyPieceA_conditional :=
  @Gdbh.PathCClassicalAssemblyChain.step7b_assemblyPieceA_conditional

/-- **Disjoint Möbius product identity**:
`μ(d₁.prod) · μ(d₂.prod) = μ((d₁ ∪ d₂).prod)`.
Source: `PathC_ClassicalAssemblyChain.lean`. -/
abbrev moebius_disjoint_prod_eq_union :=
  @Gdbh.PathCClassicalAssemblyChain.moebius_disjoint_prod_eq_union

/-! ### Section B — Paired Bonferroni indicator (P19-T1).

The product of two single-variable Bonferroni indicator inequalities
applied to `m` and `n-m` separately.
Source: `Gdbh/PathC_PairedBonferroniIndicator.lean`. -/

/-- The paired Bonferroni indicator inequality Prop. -/
abbrev PairedBonferroniIndicator :=
  Gdbh.PathCPairedBonferroniIndicator.PairedBonferroniIndicator

/-- **Closure** of `PairedBonferroniIndicator` (P19-T1). -/
abbrev pairedBonferroniIndicator_holds :=
  @Gdbh.PathCPairedBonferroniIndicator.pairedBonferroniIndicator_holds

/-! ### Section C — Paired Bonferroni sum rearrangement (P19-T3).

Pure Finset rearrangement turning the product-of-sums per `m` into a
double sum over `(d₁, d₂)` with inner pair-count.
Source: `Gdbh/PathC_PairedBonferroniSumRearrange.lean`. -/

/-- The paired Bonferroni sum-rearrangement identity Prop. -/
abbrev PairedBonferroniSumRearrange :=
  Gdbh.PathCPairedBonferroniSumRearrange.PairedBonferroniSumRearrange

/-- **Closure** of `PairedBonferroniSumRearrange` (P19-T3). -/
abbrev pairedBonferroniSumRearrange_holds :=
  @Gdbh.PathCPairedBonferroniSumRearrange.pairedBonferroniSumRearrange_holds

/-! ### Section D — Goldbach paired CRT counting (P17-T3).

For coprime positive `d₁, d₂`, the signed count of `m ∈ [1, n-1]` with
`d₁ ∣ m` and `d₂ ∣ (n - m)` differs from `n / (d₁ d₂)` by at most `1`.
Source: `Gdbh/PathC_GoldbachPairCRTCount.lean`. -/

/-- The Goldbach paired CRT counting Prop. -/
abbrev GoldbachPairCRTCount :=
  Gdbh.PathCGoldbachPairCRTCount.GoldbachPairCRTCount

/-- **Closure** of `GoldbachPairCRTCount` (P17-T3). -/
abbrev goldbachPairCRTCount_holds :=
  @Gdbh.PathCGoldbachPairCRTCount.goldbachPairCRTCount_holds

/-! ### Section E — Disjoint-pair Möbius density / union identity
(P19-T4).

For disjoint `d₁, d₂ ⊆ P` of primes, the disjoint-pair Möbius density
equals the single-set Möbius density of the union.
Source: `Gdbh/PathC_PairedMainTermAtSqrtReduction.lean`. -/

/-- Disjoint-pair Möbius density union identity (P19-T4). -/
abbrev disjoint_pair_term_eq_union :=
  @Gdbh.PathCPairedMainTermAtSqrtReduction.disjoint_pair_term_eq_union

/-! ### Section F — Paired Euler product / Brun-factor identification
(P17-T4 and P19-T28).

The paired Brun factor at sieve level `z` equals the alternating Möbius
sum over squarefree divisors built from primes in `[3, z]`.
Source: `Gdbh/PathC_PairedMainTermFromLocalDensity.lean` and
`Gdbh/PathC_MoebiusInversionRoute.lean`. -/

/-- **P17-T4 — Paired Euler product identification of the Brun
factor.** -/
abbrev paired_eulerProduct_identity_pairedBrunFactor :=
  @Gdbh.PathCPairedMainTermFromLocalDensity.paired_eulerProduct_identity_pairedBrunFactor

/-- **P19-T28 — Möbius-form of the paired Euler product.** -/
abbrev paired_eulerProduct_moebius_form :=
  @Gdbh.PathCMoebiusInversionRoute.paired_eulerProduct_moebius_form

/-! ### Section G — Bonferroni truncation tail kernel (P19-T19).

The triangle-inequality kernel for the truncation tail of the
Bonferroni signed sum, plus the term-wise `(2/3)^|d|` bound under the
hypothesis that each prime in `P` is `≥ 3`.
Source: `Gdbh/PathC_BonferroniTailKernel.lean`. -/

/-- The Bonferroni truncation tail Prop. -/
abbrev BonferroniTruncationTail :=
  Gdbh.PathCBonferroniTailKernel.BonferroniTruncationTail

/-- **Closure** of `BonferroniTruncationTail` (P19-T19). -/
abbrev bonferroniTruncationTail_holds :=
  @Gdbh.PathCBonferroniTailKernel.bonferroniTruncationTail_holds

/-- **Term-wise `(2/3)^|d|` bound** under primes `≥ 3` (P19-T19). -/
abbrev tailTerm_le_two_thirds_pow :=
  @Gdbh.PathCBonferroniTailKernel.tailTerm_le_two_thirds_pow

/-! ### Section H — Finset-attach factorisation route (P19-T30).

Pure combinatorial decomposition of a truncated disjoint-pair sum of
`f (d₁ ∪ d₂)` into a single sum over `D ⊆ P` of `f D` weighted by the
count of disjoint partitions of `D`.
Source: `Gdbh/PathC_FinsetAttachRoute.lean`. -/

/-- **Combinatorial-core**: indicator-sum factorisation through the
union map. -/
abbrev disjointPairs_indicator_sum_factorize :=
  @Gdbh.PathCFinsetAttachRoute.disjointPairs_indicator_sum_factorize

/-- **Specialisation**: Möbius-density disjoint-pair sum factorisation
through the union map. -/
abbrev disjointPairs_moebius_density_factorize :=
  @Gdbh.PathCFinsetAttachRoute.disjointPairs_moebius_density_factorize

/-! ### Section I — Kernel residual and final bridge (P19-T29).

The genuine combinatorial residual `BrunBonferroniCombinatorialKernelAtSqrt`
and the mechanical bridge to `AssemblyPieceA`.
Source: `Gdbh/PathC_AssemblyPieceAClosure.lean`. -/

/-- The combinatorial-kernel residual at sieve threshold `z = √n`. -/
abbrev BrunBonferroniCombinatorialKernelAtSqrt :=
  Gdbh.PathCAssemblyPieceAClosure.BrunBonferroniCombinatorialKernelAtSqrt

/-- The target Prop:  `AssemblyPieceA` of the paired Brun-Bonferroni
inequality at sieve threshold `z = √n`. -/
abbrev AssemblyPieceA :=
  Gdbh.PathCBrunBonferroniDecomposition.AssemblyPieceA

/-- **P19-T29 bridge**: kernel residual implies `AssemblyPieceA`. -/
abbrev assemblyPieceA_of_kernel :=
  @Gdbh.PathCAssemblyPieceAClosure.assemblyPieceA_of_kernel

/-- **P19-T29 conditional headline**: `AssemblyPieceA` provided the
kernel holds. -/
abbrev assemblyPieceA_holds_conditional :=
  @Gdbh.PathCAssemblyPieceAClosure.assemblyPieceA_holds_conditional

end BrunMaster

/-! ## The headline theorem.

The cleanest single composition in the codebase from the named
combinatorial residual to the assembly piece headline `AssemblyPieceA`,
using the master interface above. -/

/-- **Master Brun-Bonferroni assembly**: given the open residual
kernel `BrunBonferroniCombinatorialKernelAtSqrt`, derive
`AssemblyPieceA` by composing the steps via the master interface.

This is the cleanest single composition in the codebase.  The
five-line proof composes Steps 7a/7b through the master re-export
layer (no new content). -/
theorem assemblyPieceA_of_kernel_master
    (hKernel : BrunMaster.BrunBonferroniCombinatorialKernelAtSqrt) :
    BrunMaster.AssemblyPieceA := by
  -- Step 7a (PathC_ClassicalAssemblyChain) bridges kernel ⇒ AssemblyPieceA.
  -- Step 7b is the same statement, exposed conditionally.
  -- We apply Step 7a directly via the master interface.
  exact BrunMaster.step7a_assemblyPieceA_of_kernel hKernel

/-! ## Axiom audit. -/

#print axioms assemblyPieceA_of_kernel_master

/-! ## Summary sentinel. -/

/-- **P19-T36 summary** (informal sentinel).  This file is the master
re-export layer over Phases 17-19's Brun-Bonferroni infrastructure.
Every name in `BrunMaster` is a direct re-export of a previously
proved lemma; no new mathematical content is introduced.  The
headline `assemblyPieceA_of_kernel_master` composes Steps 7a/7b via
the master interface in a single tactic invocation. -/
theorem pathC_p19_t36_summary : True := trivial

end PathCBrunBonferroniMaster
end Gdbh
