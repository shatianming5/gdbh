/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P18-T1 (Phase 18 / Path C — Paired Brun factor Mertens upper
        bound at the square-root threshold)
-/
import Gdbh.PathC_PairedBrunLargeZ
import Gdbh.PathC_MertensFirstClosure
import Gdbh.PathC_ClosedReductions
import Gdbh.PathC_BrunGoldbachComposition

/-!
# Path C — P18-T1: Mertens upper bound for `pairedBrunFactor` at `√n`

This file is the **P18-T1 deliverable** in Phase 18 (Path C closure).
Its target is the named open Prop
`Gdbh.PathCPairedBrunLargeZ.PairedBrunFactorMertensUpperAtSqrt`
exposed in `Gdbh/PathC_PairedBrunLargeZ.lean`:

```
∃ C' : ℝ, ∃ N₀ : ℕ, 0 < C' ∧ ∀ n : ℕ, N₀ ≤ n →
  pairedBrunFactor (Nat.sqrt n) ≤ C' / (Real.log (n : ℝ))^2 .
```

## Strategy

The headline reduction
`Gdbh.PathCMertensSecondProof.pairedBrunMertensThirdGap_of_first_and_abel`
combines

* `Gdbh.PathCMertensFirstClosure.mertensFirstTheoremBound_holds`
  (Mertens' 1st theorem, closed axiom-clean via the von Mangoldt /
  Stirling / prime-power-tail decomposition), and

* `Gdbh.PathCClosedReductions.abelInversionMertensSecondFromFirst_holds`
  (Abel-summation arrow, closed axiom-clean from the Abel identity, log
  integral asymptotic, Mertens error integral, and integrand split),

yielding `Gdbh.PathCMertensProof.PairedBrunMertensThirdGap`:

```
∃ C > 0, ∃ z₀, ∀ z ≥ z₀,  pairedBrunFactor z ≤ C / (log z)^2 .
```

Specialised at `z = Nat.sqrt n`, with `log(Nat.sqrt n) ≥ (log n) / 4`
for `n ≥ 16`, the existing P13-T1 reduction
`Gdbh.PathCBrunGoldbachComposition.mertensPairedProductBound_pairedBrunFactor_Nat_sqrt_of_gap`
already packages this into the desired `(log n)^2`-shape:

```
∃ C₃ N₀ : ℕ, 0 < C₃ ∧
  ∀ n ≥ N₀, 2 ≤ n →  pairedBrunFactor (Nat.sqrt n) ≤ C₃ / (log n)^2 .
```

This file's contribution is the **last mile**: rewrap the natural
constant `C₃ : ℕ` as a real `(C₃ : ℝ) > 0`, and absorb the auxiliary
`2 ≤ n` into a single threshold `N₀' := max N₀ 2`.  The result is the
named open Prop in its expected shape.

## Axiom budget

Every theorem below is axiom-clean: the only axioms transitively used
are `Classical.choice`, `Quot.sound`, `propext`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine
  angew. Math. 78 (1874), 46–62 (Theorems 1 = M1, 3 = M2).
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Lemma 2.5 (the paired
  Mertens product expansion).
-/

namespace Gdbh
namespace PathCPairedBrunMertensUpper

open Real
open Gdbh.PathCMertensProof (pairedBrunFactor)
open Gdbh.PathCPairedBrunLargeZ (PairedBrunFactorMertensUpperAtSqrt)
open Gdbh.PathCGoldbachRBound (MertensPairedProductBound)
open Gdbh.PathCBrunGoldbachComposition
  (mertensPairedProductBound_pairedBrunFactor_Nat_sqrt_of_gap)
open Gdbh.PathCMertensSecondProof
  (pairedBrunMertensThirdGap_of_first_and_abel)
open Gdbh.PathCMertensFirstClosure (mertensFirstTheoremBound_holds)
open Gdbh.PathCClosedReductions (abelInversionMertensSecondFromFirst_holds)

/-! ## Section 1 — Headline closure

The proof composes:

1. `mertensFirstTheoremBound_holds` (closed: Mertens' 1st theorem),
2. `abelInversionMertensSecondFromFirst_holds` (closed: Abel arrow),
3. `pairedBrunMertensThirdGap_of_first_and_abel` (closed reduction),
4. `mertensPairedProductBound_pairedBrunFactor_Nat_sqrt_of_gap` (closed
   specialisation at `z = √n`, using `log(√n) ≥ (log n)/4` for `n ≥ 16`).

The final step rewraps the natural constant as a real and absorbs the
auxiliary `2 ≤ n` threshold. -/

/-- **P18-T1 headline theorem.**  The paired Brun factor satisfies
the Mertens upper bound at the canonical square-root threshold:

```
pairedBrunFactor (Nat.sqrt n)  ≤  C' / (log n)^2     for n ≥ N₀ .
```

Closed axiom-clean via the M1 + Abel chain, specialised at `z = √n`
through the existing P13-T1 reduction. -/
theorem pairedBrunFactorMertensUpperAtSqrt_holds :
    PairedBrunFactorMertensUpperAtSqrt := by
  -- Step 1: assemble `PairedBrunMertensThirdGap` from M1 and Abel.
  have hGap := pairedBrunMertensThirdGap_of_first_and_abel
    mertensFirstTheoremBound_holds
    abelInversionMertensSecondFromFirst_holds
  -- Step 2: specialise to `Nat.sqrt n` via the existing P13-T1 reduction.
  have hPaired :
      MertensPairedProductBound pairedBrunFactor Nat.sqrt :=
    mertensPairedProductBound_pairedBrunFactor_Nat_sqrt_of_gap hGap
  -- Step 3: unpack and reshape.
  obtain ⟨C₃, N₀, hC₃pos, hBd⟩ := hPaired
  -- The output constant is the real cast of `C₃`; the threshold absorbs `2 ≤ n`.
  refine ⟨(C₃ : ℝ), max N₀ 2, ?_, ?_⟩
  · -- `0 < (C₃ : ℝ)` since `0 < C₃ : ℕ`.
    exact_mod_cast hC₃pos
  · intro n hn
    have hN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    exact hBd n hN₀ hn2

/-! ## Section 2 — Documentation summary -/

/-- **P18-T1 summary, in proof form.**

Deliverables:

1. `pairedBrunFactorMertensUpperAtSqrt_holds` — **headline theorem**:
   closes the named open
   `Gdbh.PathCPairedBrunLargeZ.PairedBrunFactorMertensUpperAtSqrt`
   axiom-clean by composing:

   * `mertensFirstTheoremBound_holds` (Mertens' 1st theorem, closed
     via von Mangoldt + Stirling + prime-power-tail);
   * `abelInversionMertensSecondFromFirst_holds` (Abel arrow, closed
     via Abel identity + log integral + Mertens error + split);
   * `pairedBrunMertensThirdGap_of_first_and_abel` (closed reduction);
   * `mertensPairedProductBound_pairedBrunFactor_Nat_sqrt_of_gap`
     (closed specialisation, using `log(√n) ≥ (log n)/4` for `n ≥ 16`).

Axiom audit: `[Classical.choice, Quot.sound, propext]`. -/
theorem pathC_p18_t1_summary : True := trivial

end PathCPairedBrunMertensUpper
end Gdbh
