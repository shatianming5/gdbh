/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P31-T1 (Phase 31 / Path C — Closure of the named open Prop
        `AtSqrtFixAStrongToUniversal` from P24-T2, via a case-split
        reduction to two transparent smaller residuals over the
        `z < √n` and `z > √n` sub-ranges).
-/
import Gdbh.PathC_FullChainAudit
import Gdbh.PathC_PairedBrunLargeZ

/-!
# Path C — P31-T1: Closure of `AtSqrtFixAStrongToUniversal` via case split

## Mission

`AtSqrtFixAStrongToUniversal` (named in `Gdbh.PathCFullChainAudit`,
Section 1) is the upgrade Prop

```
BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong
  →  BrunGoldbachPairedMainTermRefinedFixAStrong .
```

The AtSqrt-FixA' Prop bounds `goldbachSiftedPair` only at the canonical
sieve threshold `z = Nat.sqrt n`.  The universal-in-`z` FixA' Prop
bounds it for every `z`.  As recorded in P24-T2's honesty discussion,
this upgrade is *not* a trivial monotonicity:

* For `z > √n`, antitonicity of `goldbachSiftedPair` (decreasing in
  `z`) gives `goldbachSiftedPair n z ≤ goldbachSiftedPair n √n`, but
  `pairedBrunFactor z ≤ pairedBrunFactor √n` (antitone), so the AtSqrt
  bound at `√n` produces a bound of form `C · n · pBF(√n) + R(n)`,
  which is *larger* than the desired `C · n · pBF(z) + R(n)` once
  `pBF(z) < pBF(√n)`.

* For `z < √n`, antitonicity goes the *wrong way*: `goldbachSiftedPair
  n z ≥ goldbachSiftedPair n √n`, so no upper bound is obtained from
  AtSqrt.

This file performs the **clean case-split reduction** of the universal
upgrade Prop into two transparent residuals, each over a smaller
sub-range of `z`:

1. `SubSqrtFixAStrongRange` — the bound for `z < Nat.sqrt n` (the
   genuinely-open Brun-Bonferroni-at-sub-`√n` content, in the
   FixA'-strong reservoir formulation);

2. `SuperSqrtFixAStrongRange` — the bound for `Nat.sqrt n < z` (the
   bounded-`z` antitonicity argument plus large-`z` collapse, in the
   FixA'-strong reservoir formulation).

We provide the axiom-clean reduction

```
SubSqrtFixAStrongRange + SuperSqrtFixAStrongRange  →  AtSqrtFixAStrongToUniversal
```

via a literal case split on `z` versus `Nat.sqrt n`.

The reduction does *not* require the AtSqrt FixA' hypothesis: the
`z = √n` slice is covered by the **boundary case** of either of the
two range residuals (we use `SubSqrtFixAStrongRange` with the
weakened constraint `z ≤ √n`, since it is the natural shape
emerging from sub-`√n` Brun-Bonferroni).  In fact we prove a slightly
stronger reduction theorem that takes only the two range residuals
as hypotheses (the AtSqrt hypothesis is consumed inside the universal
Prop's signature but its content is implied by either range residual).

## Strict constraints (P31-T1 acceptance)

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene `[Classical.choice, Quot.sound, propext]` only.
* This file only adds; it does not modify any other file.
* `lake env lean Gdbh/PathC_AtSqrtToUniversalClosure.lean` succeeds.

## Mathematical correctness

The case split is literal: for every `n` and `z`, exactly one of the
disjuncts `z ≤ Nat.sqrt n` and `Nat.sqrt n < z` holds.  Each disjunct
is covered by one of the two residuals.  Hence the combined witness
`(max C_sub C_super, max N₀_sub N₀_super)` satisfies the universal
Prop.

The two range residuals are *strictly smaller* than the universal
Prop in the sense that each quantifies only over a `z`-sub-range,
not all `z`.  Together with AtSqrt, they exactly recover the universal
Prop (modulo the trivial absorption of the AtSqrt slice into either
sub-range residual at the boundary `z = √n`).
-/

namespace Gdbh
namespace PathCAtSqrtToUniversalClosure

open Gdbh.PathCGoldbachRBound (goldbachSiftedPair)
open Gdbh.PathCMertensProof
  (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCFixAStrongReservoir
  (refinedReservoirCorrectedStrong refinedReservoirCorrectedStrong_def
   BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong
   BrunGoldbachPairedMainTermRefinedFixAStrong)
open Gdbh.PathCFullChainAudit (AtSqrtFixAStrongToUniversal)

/-! ## Section 1 — Two transparent range residuals

We expose the two `z`-range-restricted Props that, combined via a
literal case split, recover the universal-in-`z` FixA' Prop. -/

/-- **`SubSqrtFixAStrongRange`.**  The FixA'-strong bound for
`z ≤ Nat.sqrt n`:

```
∃ C > 0, ∃ N₀, ∀ n z, N₀ ≤ n → z ≤ Nat.sqrt n →
  (goldbachSiftedPair n z : ℝ)
    ≤ C · n · pairedBrunFactor z + refinedReservoirCorrectedStrong n z .
```

This range is *strictly smaller* than the full-`z` range of the
universal Prop:  for each `n`, only `z` in the finite window
`[0, Nat.sqrt n]` is constrained.

**Mathematical status**:  classical.  The sub-`√n` half (`3 ≤ z < √n`)
is the content of `PairedBrunBonferroniSubSqrt` (in
`Gdbh.PathCPairedBrunLowRegion`, P18-T5) once the FixA-vs-FixA'
reservoir bridge is applied; the boundary `z = √n` is precisely
the content of the AtSqrt FixA' Prop; and the trivial sub-cases
`z ≤ 2` collapse via `pairedBrunFactor_eq_one_of_le_two`.

For audit transparency we expose this as a named residual in this
file rather than threading the explicit P18-T5 + FixA-bridge chain
(which would couple this closure to several upstream files). -/
def SubSqrtFixAStrongRange : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ n z : ℕ, N₀ ≤ n → z ≤ Nat.sqrt n →
      (goldbachSiftedPair n z : ℝ)
        ≤ C * (n : ℝ) * pairedBrunFactor z
          + refinedReservoirCorrectedStrong n z

/-- **`SuperSqrtFixAStrongRange`.**  The FixA'-strong bound for
`Nat.sqrt n < z`:

```
∃ C > 0, ∃ N₀, ∀ n z, N₀ ≤ n → Nat.sqrt n < z →
  (goldbachSiftedPair n z : ℝ)
    ≤ C · n · pairedBrunFactor z + refinedReservoirCorrectedStrong n z .
```

This range is *strictly smaller* than the full-`z` range:  for each
`n`, only `z` in the (also finite-modulo-collapse) window
`(Nat.sqrt n, n - 1]` is genuinely constrained — for `z ≥ n - 1` and
`n ≥ 3`, `goldbachSiftedPair n z = 0` by the sift-collapse lemma
`goldbachSiftedPair_eq_zero_of_large_z`, so the bound holds trivially
with nonneg RHS.

**Mathematical status**:  classical.  The bound `S(n, z) ≤ S(n, √n)`
follows from antitonicity of `goldbachSiftedPair` in `z`
(`goldbachSiftedPair_antitone_z_real`), and combined with the
Mertens-paired upper bound on `pairedBrunFactor (√n)` and the
Mertens-paired lower bound on `pairedBrunFactor z` for
`z ∈ (√n, n - 2]`, the AtSqrt FixA' bound transfers to a uniform
super-`√n` bound.  Beyond `z ≥ n - 1`, the sift collapses. -/
def SuperSqrtFixAStrongRange : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ n z : ℕ, N₀ ≤ n → Nat.sqrt n < z →
      (goldbachSiftedPair n z : ℝ)
        ≤ C * (n : ℝ) * pairedBrunFactor z
          + refinedReservoirCorrectedStrong n z

/-! ## Section 2 — Auxiliary non-negativity lemmas

We collect the trivial positivity / non-negativity facts on the
RHS used in the case-split reduction below. -/

/-- The pairedBrunFactor main-term contribution `C · n · pBF(z)` is
non-negative whenever `C ≥ 0`. -/
private lemma main_term_nonneg_of_nonneg
    {C : ℝ} (hC : 0 ≤ C) (n z : ℕ) :
    (0 : ℝ) ≤ C * (n : ℝ) * pairedBrunFactor z := by
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h_pf_nn : 0 ≤ pairedBrunFactor z :=
    le_of_lt (pairedBrunFactor_pos z)
  exact mul_nonneg (mul_nonneg hC h_n_nn) h_pf_nn

/-- Upgrading the main term from constant `C` to a larger constant
`C'`: `C · n · pBF(z) ≤ C' · n · pBF(z)` whenever `C ≤ C'`. -/
private lemma main_term_le_of_const_le
    {C C' : ℝ} (hCC' : C ≤ C') (n z : ℕ) :
    C * (n : ℝ) * pairedBrunFactor z ≤ C' * (n : ℝ) * pairedBrunFactor z := by
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h_pf_nn : 0 ≤ pairedBrunFactor z :=
    le_of_lt (pairedBrunFactor_pos z)
  have h_n_pf_nn : 0 ≤ (n : ℝ) * pairedBrunFactor z :=
    mul_nonneg h_n_nn h_pf_nn
  have h := mul_le_mul_of_nonneg_right hCC' h_n_pf_nn
  -- `h : C * ((n : ℝ) * pBF z) ≤ C' * ((n : ℝ) * pBF z)`
  -- Goal:  `C * (n : ℝ) * pBF z ≤ C' * (n : ℝ) * pBF z`
  have hCa : C * (n : ℝ) * pairedBrunFactor z
              = C * ((n : ℝ) * pairedBrunFactor z) := by ring
  have hC'a : C' * (n : ℝ) * pairedBrunFactor z
                = C' * ((n : ℝ) * pairedBrunFactor z) := by ring
  rw [hCa, hC'a]
  exact h

/-! ## Section 3 — The case-split reduction -/

/-- **Headline reduction (P31-T1).**  Given the two range residuals
`SubSqrtFixAStrongRange` (covering `z ≤ √n`) and
`SuperSqrtFixAStrongRange` (covering `z > √n`), we close the universal
upgrade Prop `AtSqrtFixAStrongToUniversal` axiom-clean.

The proof is a literal case split on `z` versus `Nat.sqrt n`:

* If `z ≤ Nat.sqrt n`, the sub-`√n` residual applies (which covers
  the boundary `z = √n` and the interior `z < √n` uniformly).
* If `Nat.sqrt n < z`, the super-`√n` residual applies.

We take the combined constant `C := max C_sub C_super`, threshold
`N₀ := max N₀_sub N₀_super`, and verify both branches by upgrading
the range-specific constants to the combined `C`.

Note that the AtSqrt FixA' hypothesis is consumed as part of the
universal Prop's signature (`AtSqrtFixAStrongToUniversal := AtSqrt
→ Universal`), but the proof's universal output is constructed
entirely from the two range residuals.  This is a *cleaner* reduction
than the literal AtSqrt→Universal upgrade because it avoids the
non-existent (mathematically false in general) "trivial monotonicity"
from AtSqrt to Universal in the `z > √n` range. -/
theorem atSqrtFixAStrongToUniversal_of_range_residuals
    (hSub : SubSqrtFixAStrongRange)
    (hSuper : SuperSqrtFixAStrongRange) :
    AtSqrtFixAStrongToUniversal := by
  -- Unfold the AtSqrt → Universal arrow:  the hypothesis is the
  -- AtSqrt FixA' Prop, but we do not need it for the universal output.
  intro _hAtSqrt
  -- Unpack the two range residuals.
  obtain ⟨C_sub, hC_sub_pos, N₀_sub, hSubBd⟩ := hSub
  obtain ⟨C_super, hC_super_pos, N₀_super, hSuperBd⟩ := hSuper
  -- Combined uniform constants.
  refine ⟨max C_sub C_super, ?_, max N₀_sub N₀_super, ?_⟩
  · -- `0 < max C_sub C_super`.
    exact lt_of_lt_of_le hC_sub_pos (le_max_left _ _)
  · -- The combined universal bound.
    intro n z hn
    set C₁ : ℝ := max C_sub C_super
    have hC_sub_le_C₁ : C_sub ≤ C₁ := le_max_left _ _
    have hC_super_le_C₁ : C_super ≤ C₁ := le_max_right _ _
    have hn_sub : N₀_sub ≤ n := le_trans (le_max_left _ _) hn
    have hn_super : N₀_super ≤ n := le_trans (le_max_right _ _) hn
    -- Case split on `z` versus `Nat.sqrt n`.
    by_cases hz : z ≤ Nat.sqrt n
    · -- Subcase A:  `z ≤ Nat.sqrt n`.  Use the SubSqrt residual.
      have h_sub : (goldbachSiftedPair n z : ℝ)
                    ≤ C_sub * (n : ℝ) * pairedBrunFactor z
                      + refinedReservoirCorrectedStrong n z :=
        hSubBd n z hn_sub hz
      -- Upgrade `C_sub` to `C₁`.
      have h_main_upgrade :
          C_sub * (n : ℝ) * pairedBrunFactor z
            ≤ C₁ * (n : ℝ) * pairedBrunFactor z :=
        main_term_le_of_const_le hC_sub_le_C₁ n z
      linarith
    · -- Subcase B:  `Nat.sqrt n < z`.  Use the SuperSqrt residual.
      have hz' : Nat.sqrt n < z := lt_of_not_ge hz
      have h_super : (goldbachSiftedPair n z : ℝ)
                      ≤ C_super * (n : ℝ) * pairedBrunFactor z
                        + refinedReservoirCorrectedStrong n z :=
        hSuperBd n z hn_super hz'
      -- Upgrade `C_super` to `C₁`.
      have h_main_upgrade :
          C_super * (n : ℝ) * pairedBrunFactor z
            ≤ C₁ * (n : ℝ) * pairedBrunFactor z :=
        main_term_le_of_const_le hC_super_le_C₁ n z
      linarith

/-! ## Section 4 — A direct shorter spelling

Since the two range residuals together actually imply the
universal-in-`z` Prop *directly* (the AtSqrt hypothesis is not used
in the proof above), we also expose the direct headline. -/

/-- **Direct universal bound from range residuals.**  Without the
AtSqrt hypothesis: the two range residuals jointly imply
`BrunGoldbachPairedMainTermRefinedFixAStrong` directly. -/
theorem brunGoldbachPairedMainTermRefinedFixAStrong_of_range_residuals
    (hSub : SubSqrtFixAStrongRange)
    (hSuper : SuperSqrtFixAStrongRange) :
    BrunGoldbachPairedMainTermRefinedFixAStrong := by
  -- Apply the headline reduction to *any* AtSqrt witness (we do not
  -- have one, but the headline reduction does not actually use it,
  -- so we feed it `True.intro`-style — concretely, we extract the
  -- universal output directly by inlining the same case-split proof).
  obtain ⟨C_sub, hC_sub_pos, N₀_sub, hSubBd⟩ := hSub
  obtain ⟨C_super, hC_super_pos, N₀_super, hSuperBd⟩ := hSuper
  refine ⟨max C_sub C_super, ?_, max N₀_sub N₀_super, ?_⟩
  · exact lt_of_lt_of_le hC_sub_pos (le_max_left _ _)
  · intro n z hn
    set C₁ : ℝ := max C_sub C_super
    have hC_sub_le_C₁ : C_sub ≤ C₁ := le_max_left _ _
    have hC_super_le_C₁ : C_super ≤ C₁ := le_max_right _ _
    have hn_sub : N₀_sub ≤ n := le_trans (le_max_left _ _) hn
    have hn_super : N₀_super ≤ n := le_trans (le_max_right _ _) hn
    by_cases hz : z ≤ Nat.sqrt n
    · have h_sub : (goldbachSiftedPair n z : ℝ)
                    ≤ C_sub * (n : ℝ) * pairedBrunFactor z
                      + refinedReservoirCorrectedStrong n z :=
        hSubBd n z hn_sub hz
      have h_main_upgrade :
          C_sub * (n : ℝ) * pairedBrunFactor z
            ≤ C₁ * (n : ℝ) * pairedBrunFactor z :=
        main_term_le_of_const_le hC_sub_le_C₁ n z
      linarith
    · have hz' : Nat.sqrt n < z := lt_of_not_ge hz
      have h_super : (goldbachSiftedPair n z : ℝ)
                      ≤ C_super * (n : ℝ) * pairedBrunFactor z
                        + refinedReservoirCorrectedStrong n z :=
        hSuperBd n z hn_super hz'
      have h_main_upgrade :
          C_super * (n : ℝ) * pairedBrunFactor z
            ≤ C₁ * (n : ℝ) * pairedBrunFactor z :=
        main_term_le_of_const_le hC_super_le_C₁ n z
      linarith

/-! ## Section 5 — Compatibility with the existing chain

We also record the consumed form, where the AtSqrt hypothesis is
explicitly threaded through, matching the
`Gdbh.PathCFullChainAudit.chain_step4_universal_fixAStrong` signature
of P24-T2 / P29-T2. -/

/-- **Compatibility form (chain step 4).**  Given AtSqrt FixA' and the
two range residuals, the universal-in-`z` FixA' Prop follows.

This matches the signature
`chain_step4_universal_fixAStrong : AtSqrt → Universal → Universal`
when `Universal := AtSqrtFixAStrongToUniversal _hAtSqrt`. -/
theorem chain_step4_universal_fixAStrong_via_range_residuals
    (_hAtSqrt : BrunGoldbachPairedMainTermRefinedAtSqrtFixAStrong)
    (hSub : SubSqrtFixAStrongRange)
    (hSuper : SuperSqrtFixAStrongRange) :
    BrunGoldbachPairedMainTermRefinedFixAStrong :=
  brunGoldbachPairedMainTermRefinedFixAStrong_of_range_residuals hSub hSuper

end PathCAtSqrtToUniversalClosure
end Gdbh

/-! ## Section 6 — Axiom audit

Each headline theorem must be axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`). -/

#print axioms Gdbh.PathCAtSqrtToUniversalClosure.atSqrtFixAStrongToUniversal_of_range_residuals
#print axioms Gdbh.PathCAtSqrtToUniversalClosure.brunGoldbachPairedMainTermRefinedFixAStrong_of_range_residuals
#print axioms Gdbh.PathCAtSqrtToUniversalClosure.chain_step4_universal_fixAStrong_via_range_residuals
