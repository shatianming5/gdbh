/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P13-T1 (Phase 13 / Path C closure — coordinated composition of
        the three Brun-Goldbach sub-Props for the pinned triple
        `(pairedBrunFactor, 0, Nat.sqrt)`)
-/
import Gdbh.PathC_GoldbachRBound
import Gdbh.PathC_BrunErrorDecayProof
import Gdbh.PathC_BrunMainProof
import Gdbh.PathC_MertensThirdProof
import Gdbh.PathC_MertensSecondProof

/-!
# Path C — P13-T1: coordinated closure attempt for `GoldbachRepresentationBound`

This file is the **P13-T1 deliverable** in Phase 13 (final Path C
closure).  It attempts a **coordinated** closure of the three
Brun-Goldbach sub-Props from `Gdbh/PathC_GoldbachRBound.lean` by pinning
a *single* consistent triple of witnesses

```
M       := pairedBrunFactor     -- the genuine paired Brun main-term factor
B       := fun _ _ => 0          -- the trivial zero error reservoir
zChoice := Nat.sqrt              -- the classical Brun √n sieve threshold
```

and trying to prove all three sub-Props for these *same* witnesses.  The
mission is honest discovery: surface a new false-Prop, or identify the
truly atomic mathlib gap.

## P13-T1 finding (the catch carries over)

**`BrunGoldbachMainTerm pairedBrunFactor (fun _ _ => 0)` is
conditionally false**, by the *same* mechanism that P9-T2 used to
disprove `BrunMainTerm pairedBrunFactor brunErrorWitness` for the
*single* sift:

* `goldbachSiftedPair 2 z = 1` for every sieve threshold `z`
  (the integer `m = 1` has no prime divisors at all, so it survives every
  sieve; combined with `n - m = 1` likewise, we get `m = 1` always in the
  paired sifted set);
* `pairedBrunFactor z ≤ C / (log z)^2 → 0` as `z → ∞`
  (this is the open named Prop `PairedBrunMertensThirdGap`).

Hence for *any* candidate constant `C₁ > 0`, the inequality

```
1 = goldbachSiftedPair 2 z  ≤  C₁ · 2 · pairedBrunFactor z + 0
```

fails for `z` sufficiently large.  The conditional disproof is recorded
as `pairedBrunMertensThirdGap_disproves_brunGoldbachMainTerm_zero`.

**Consequence.**  The pinned triple `(pairedBrunFactor, 0, Nat.sqrt)`
**cannot** simultaneously close all three sub-Props.  This is the
*same* asymmetry already documented at the single-sift layer in
`Gdbh/PathC_BrunMainProof.lean`: the `B ≡ 0` reservoir absorbs the
analytic content into the *multiplicative* term, where the asymptotic
decay of `pairedBrunFactor` forbids domination of even the smallest
non-vacuous lower bound `goldbachSiftedPair 2 z = 1`.

## Satisfiability assessment for the pinned triple

| sub-Prop                                                                       | status                                                                                                             |
|---|---|
| `BrunGoldbachMainTerm pairedBrunFactor (fun _ _ => 0)`                        | **conditionally false** (assuming `PairedBrunMertensThirdGap`); see `pairedBrunMertensThirdGap_disproves_brunGoldbachMainTerm_zero` |
| `BrunGoldbachErrorTerm (fun _ _ => 0) Nat.sqrt`                                | **trivially true**; reuses `Gdbh.PathCBrunErrorDecayProof.brunGoldbachErrorTerm_concrete`                          |
| `MertensPairedProductBound pairedBrunFactor Nat.sqrt`                          | **reduces** to `PairedBrunMertensThirdGap` via the gap `pairedBrunFactor z ≤ C/(log z)²` and `log(√n) ≥ (log n)/4` |

The middle entry is the *only* sub-Prop that closes cleanly for the
pinned triple.  The first entry is asymptotically incompatible with the
zero reservoir; the third reduces (mechanically) to the named open gap.

## Reduced atomic gap structure

After P13-T1, the *coordinated* closure of `GoldbachRepresentationBound`
via the pinned triple requires the following named open inputs:

1. **`BrunGoldbachPairedMainTerm`** — a new named open Prop, defined
   below as `BrunGoldbachMainTerm pairedBrunFactor (fun _ _ => 0)`.
   This Prop is conditionally *false* (per the P13-T1 catch), so it
   cannot itself be the atomic gap; rather, it documents that the
   coordinated triple is *infeasible* with the zero reservoir.  The
   honest atomic gap for the main-term piece is therefore the
   *refactored* form `BrunGoldbachMainTerm pairedBrunFactor (fun n _ =>
   (n : ℝ))` (already closed axiom-cleanly by
   `Gdbh.PathCBrunMainProof.brunMainTerm_pairedBrunFactor_worstCaseError`'s
   *paired* analogue — see `brunGoldbachMainTerm_pairedBrunFactor_worstCaseError`
   below) — or, equivalently, the analytic Brun paired sieve estimate
   with a *non-zero* combinatorial reservoir.

2. **`MertensFirstTheoremBound`** — Mertens' 1st theorem
   `∑_{p ≤ z} log p / p = log z + O(1)`.  Together with
   `AbelInversionMertensSecondFromFirst` (the Abel-summation arrow),
   this implies `PairedBrunMertensThirdGap` and hence
   `MertensPairedProductBound pairedBrunFactor Nat.sqrt`.

The third sub-Prop is the **trivial** error-term closure already
delivered by P11-T2.

## Coordinated assembly

We expose:

* `brunGoldbachErrorTerm_zero_Nat_sqrt` — trivial closure of the error
  sub-Prop at the pinned triple (delegates to P11-T2).
* `mertensPairedProductBound_pairedBrunFactor_Nat_sqrt_of_gap` —
  mechanical reduction of the Mertens sub-Prop at the pinned triple to
  `PairedBrunMertensThirdGap`.
* `BrunGoldbachPairedMainTerm` — the new named (conditionally false)
  Prop pinning the main-term sub-Prop at the pinned triple.
* `goldbachRepresentationBound_of_coordinated` — the **coordinated
  assembly** theorem: from `BrunGoldbachPairedMainTerm`,
  `MertensFirstTheoremBound`, `AbelInversionMertensSecondFromFirst`,
  and the elementary small-sieve side condition for `Nat.sqrt`,
  conclude `GoldbachRepresentationBound`.

The assembly is *honest*: it does not pretend to prove
`BrunGoldbachPairedMainTerm` unconditionally (it cannot, per the P13-T1
catch), but it isolates the *exact* missing ingredient.  The final
honest form of the closure replaces the zero reservoir with the
worst-case reservoir `B(n, z) := n`, restoring axiom-clean closability
of the main-term piece while shifting the analytic burden onto the
error-term piece (the *honest* Brun combinatorial estimate
`(π(z))^k/k! ≤ C·n/(log n)²`).

## Axiom budget

Every theorem below is axiom-clean: only `Classical.choice`, `Quot.sound`,
`propext` are transitively used.
-/

namespace Gdbh
namespace PathCBrunGoldbachComposition

open Real Finset
open Gdbh.PathCGoldbachRBound
  (goldbachSiftedPair goldbachSiftedPairSet mem_goldbachSiftedPairSet
   goldbachSiftedPair_le
   BrunGoldbachMainTerm BrunGoldbachErrorTerm MertensPairedProductBound
   goldbachRepresentationBound_of_brunComponents)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos
  pairedBrunFactor_le_one PairedBrunMertensThirdGap)
open Gdbh.PathCBrunMainProof (pairedBrunFactor_isBrunMainTermFactor
  pairedBrunFactor_le_one_third_of_three_le)
open Gdbh.PathCBrunErrorDecayProof
  (brunGoldbachErrorTerm_concrete brunGoldbachZChoice
   brunGoldbachErrorWitness)
open Gdbh.PathCMertensSecondProof
  (MertensFirstTheoremBound AbelInversionMertensSecondFromFirst
   pairedBrunMertensThirdGap_of_first_and_abel)
open Gdbh.PathCTwinAsymptotic
  (goldbachRepresentationCount GoldbachRepresentationBound)

/-! ## Section 1 — The catch witness: `goldbachSiftedPair 2 z = 1`

The integer `m = 1` lies in `[1, 1] = Finset.Icc 1 (2 - 1)`, and since
`1` has no prime divisors at all (`p ∣ 1 ↔ p = 1`, and no prime is `1`),
the paired-sift condition holds vacuously at both `m = 1` and `n - m =
1`.  Hence the paired sifted set at `n = 2` is `{1}` for every `z`. -/

/-- For every `z`, the paired sifted set at `n = 2` is the singleton
`{1}`. -/
theorem goldbachSiftedPairSet_two (z : ℕ) :
    goldbachSiftedPairSet 2 z = ({1} : Finset ℕ) := by
  classical
  apply Finset.ext
  intro m
  rw [mem_goldbachSiftedPairSet, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hm1, hmN⟩, _, _⟩
    -- `1 ≤ m ≤ 2 - 1 = 1` forces `m = 1`.
    exact Nat.le_antisymm hmN hm1
  · rintro rfl
    refine ⟨⟨le_refl 1, le_refl 1⟩, ?_, ?_⟩
    · -- No prime divides `1`.
      intro p _ hpr hpd
      exact (Nat.Prime.one_lt hpr).ne' (Nat.eq_one_of_dvd_one hpd)
    · -- `2 - 1 = 1`, again no prime divides `1`.
      intro p _ hpr hpd
      exact (Nat.Prime.one_lt hpr).ne' (Nat.eq_one_of_dvd_one hpd)

/-- **The catch witness.**  `goldbachSiftedPair 2 z = 1` for every
sieve threshold `z`. -/
theorem goldbachSiftedPair_two (z : ℕ) : goldbachSiftedPair 2 z = 1 := by
  unfold goldbachSiftedPair
  rw [goldbachSiftedPairSet_two]
  simp

/-! ## Section 2 — Conditional disproof of
`BrunGoldbachMainTerm pairedBrunFactor (fun _ _ => 0)`

Assuming `PairedBrunMertensThirdGap`, we show that for every candidate
constant `C₁ > 0`, taking `n = 2` and `z` large enough forces a
contradiction with

```
goldbachSiftedPair 2 z = 1  ≤  C₁ · 2 · pairedBrunFactor z + 0 .
```

The structure of the proof exactly mirrors
`Gdbh.PathCBrunMainProof.pairedBrunMertensThirdGap_disproves_brunMain`.
-/

/-- **Conditional impossibility — the P13-T1 catch.**  Assuming the
named open Prop `PairedBrunMertensThirdGap`, the candidate sub-Prop
`BrunGoldbachMainTerm pairedBrunFactor (fun _ _ => 0)` is **false**.

Proof sketch.  Suppose for contradiction we have `C₁ > 0` with the
paired-sift main-term inequality.  Specialise to `n = 2` (legal because
`0 < 2`): `goldbachSiftedPair 2 z ≤ C₁ · 2 · pairedBrunFactor z + 0`.
By `goldbachSiftedPair_two`, the left-hand side equals `1`.  By the
Mertens gap, `pairedBrunFactor z ≤ C / (log z)^2 → 0` as `z → ∞`.
Choose `z` large enough that `(log z)^2 > 2·C·C₁ + 1`; then
`C₁ · 2 · pairedBrunFactor z ≤ 2·C₁·C / (log z)^2 < 1`, contradicting
the inequality. -/
theorem pairedBrunMertensThirdGap_disproves_brunGoldbachMainTerm_zero
    (hGap : PairedBrunMertensThirdGap) :
    ¬ BrunGoldbachMainTerm pairedBrunFactor (fun _ _ => (0 : ℝ)) := by
  rintro ⟨_hFactor, C₁, hC₁pos, hBound⟩
  obtain ⟨C, z₀, hCpos, hGapBound⟩ := hGap
  -- We pick a real threshold `L` with `(log L)^2 > 2·C·C₁`.
  -- Concretely `L := exp(√(2·C·C₁ + 1) + 1)`.
  set s : ℝ := Real.sqrt (2 * C * C₁ + 1) + 1 with hs_def
  have h2CC₁_nonneg : 0 ≤ 2 * C * C₁ := by
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hCpos) hC₁pos
    linarith
  have h2CC₁₁_pos : 0 < 2 * C * C₁ + 1 := by linarith
  have hsqrt_nn : 0 ≤ Real.sqrt (2 * C * C₁ + 1) := Real.sqrt_nonneg _
  have hs_pos : 0 < s := by
    have : (0 : ℝ) < 1 := by norm_num
    linarith
  set L : ℝ := Real.exp s with hL_def
  have hL_pos : 0 < L := Real.exp_pos s
  have hL_gt_one : 1 < L := by
    rw [hL_def]
    have : Real.exp 0 < Real.exp s := Real.exp_lt_exp.mpr hs_pos
    simpa using this
  -- Choose `z := max (Nat.ceil L) z₀ + 1`.
  set z : ℕ := max (Nat.ceil L) z₀ + 1 with hz_def
  have hz_ge_z₀ : z₀ ≤ z := by
    have : z₀ ≤ max (Nat.ceil L) z₀ := le_max_right _ _
    omega
  have hz_real_gt_L : L < (z : ℝ) := by
    have h1 : L ≤ (Nat.ceil L : ℝ) := Nat.le_ceil L
    have h2 : (Nat.ceil L : ℝ) ≤ ((z - 1 : ℕ) : ℝ) := by
      have : Nat.ceil L ≤ z - 1 := by
        have hz1 : Nat.ceil L + 1 ≤ z := by
          calc Nat.ceil L + 1
              ≤ max (Nat.ceil L) z₀ + 1 := by
                exact Nat.add_le_add_right (le_max_left _ _) 1
            _ = z := by rw [hz_def]
        omega
      exact_mod_cast this
    have h3 : ((z - 1 : ℕ) : ℝ) < (z : ℝ) := by
      have hz_pos : 1 ≤ z := by
        rw [hz_def]; exact Nat.succ_le_succ (Nat.zero_le _)
      have hcast : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
        rw [Nat.cast_sub hz_pos]; push_cast; ring
      rw [hcast]; linarith
    linarith
  have hz_pos_real : (0 : ℝ) < (z : ℝ) := by linarith
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by linarith
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  -- From `L < z`, deduce `s = log L < log z`.
  have hs_lt_logz : s < Real.log (z : ℝ) := by
    have hLogLt : Real.log L < Real.log (z : ℝ) :=
      Real.log_lt_log hL_pos hz_real_gt_L
    rwa [hL_def, Real.log_exp] at hLogLt
  have hsqrt_lt_logz :
      Real.sqrt (2 * C * C₁ + 1) < Real.log (z : ℝ) := by
    have h_lt_s : Real.sqrt (2 * C * C₁ + 1) < s := by
      rw [hs_def]; linarith
    linarith
  -- Hence `(log z)^2 > 2·C·C₁ + 1`.
  have hlogz_sq_gt : 2 * C * C₁ + 1 < (Real.log (z : ℝ))^2 := by
    have h_sqrt_sq : Real.sqrt (2 * C * C₁ + 1) ^ 2 = 2 * C * C₁ + 1 :=
      Real.sq_sqrt (le_of_lt h2CC₁₁_pos)
    have h_sqrt_nn : 0 ≤ Real.sqrt (2 * C * C₁ + 1) := Real.sqrt_nonneg _
    have hlogz_nn : 0 ≤ Real.log (z : ℝ) := le_of_lt hlogz_pos
    have := sq_lt_sq' (by linarith : -Real.log (z : ℝ) < Real.sqrt (2 * C * C₁ + 1))
                        hsqrt_lt_logz
    rw [h_sqrt_sq] at this
    linarith
  -- Apply the paired-sift main inequality at n=2, z.
  have hN_pos : (0 : ℕ) < 2 := by norm_num
  have hMain₀ := hBound 2 z hN_pos
  -- Cast the LHS = 1.
  have hSP_two : (goldbachSiftedPair 2 z : ℝ) = 1 := by
    have := goldbachSiftedPair_two z
    exact_mod_cast this
  rw [hSP_two] at hMain₀
  -- `1 ≤ C₁ · 2 · pairedBrunFactor z + 0`.
  have hMainSimp : (1 : ℝ) ≤ C₁ * 2 * pairedBrunFactor z := by
    have h_cast : ((2 : ℕ) : ℝ) = 2 := by norm_cast
    rw [h_cast] at hMain₀
    linarith
  -- Now bound the right-hand side via the gap.
  have hMertensZ : pairedBrunFactor z ≤ C / (Real.log (z : ℝ))^2 :=
    hGapBound z hz_ge_z₀
  have hpBF_nn : (0 : ℝ) ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
  have hC₁_two_nn : 0 ≤ C₁ * 2 := by linarith
  have hRHS_le : C₁ * 2 * pairedBrunFactor z
      ≤ C₁ * 2 * C / (Real.log (z : ℝ))^2 := by
    have h1 : C₁ * 2 * pairedBrunFactor z
        ≤ C₁ * 2 * (C / (Real.log (z : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hMertensZ hC₁_two_nn
    have h2 : C₁ * 2 * (C / (Real.log (z : ℝ))^2)
        = C₁ * 2 * C / (Real.log (z : ℝ))^2 := by ring
    linarith
  -- And `(C₁ · 2 · C) / (log z)^2 < 1` because
  -- `(log z)^2 > 2·C·C₁ + 1 > 2·C·C₁ = C₁·2·C`.
  have hlogz_sq_pos : 0 < (Real.log (z : ℝ))^2 := by positivity
  have h2CC₁_eq : 2 * C * C₁ = C₁ * 2 * C := by ring
  have hlogz_sq_gt_C₁2C : C₁ * 2 * C < (Real.log (z : ℝ))^2 := by
    rw [← h2CC₁_eq]; linarith
  have hRHS_lt_one : C₁ * 2 * C / (Real.log (z : ℝ))^2 < 1 := by
    rw [div_lt_one hlogz_sq_pos]
    exact hlogz_sq_gt_C₁2C
  linarith [hMainSimp, hRHS_le, hRHS_lt_one]

/-! ## Section 3 — Trivial closure of `BrunGoldbachErrorTerm 0 Nat.sqrt`

`brunGoldbachErrorTerm_concrete` from P11-T2 already provides the
closure for `(brunGoldbachErrorWitness, brunGoldbachZChoice) =
(fun _ _ => 0, Nat.sqrt)`.  We just rephrase it here at the pinned
triple. -/

/-- **Pinned-triple closure of `BrunGoldbachErrorTerm`.**  At the pinned
witness `B := fun _ _ => 0`, `zChoice := Nat.sqrt`, the
`BrunGoldbachErrorTerm` sub-Prop holds with `C₂ = 1`, `N₀ = 3`.

This delegates to `Gdbh.PathCBrunErrorDecayProof.brunGoldbachErrorTerm_concrete`. -/
theorem brunGoldbachErrorTerm_zero_Nat_sqrt :
    BrunGoldbachErrorTerm (fun _ _ => (0 : ℝ)) Nat.sqrt := by
  -- `brunGoldbachErrorWitness ≡ fun _ _ => 0` and `brunGoldbachZChoice ≡ Nat.sqrt`.
  have h := brunGoldbachErrorTerm_concrete
  -- Unfold the definitional equalities to match `(fun _ _ => 0, Nat.sqrt)`.
  -- `brunGoldbachErrorWitness` is by definition `fun _ _ => 0`.
  -- `brunGoldbachZChoice` is by definition `Nat.sqrt`.
  exact h

/-! ## Section 4 — Reduction of `MertensPairedProductBound pairedBrunFactor Nat.sqrt`

We show that the named open Prop `PairedBrunMertensThirdGap` (i.e.
`pairedBrunFactor z ≤ C / (log z)^2`) implies
`MertensPairedProductBound pairedBrunFactor Nat.sqrt`.

The argument uses `log(Nat.sqrt n) ≥ (log n)/4` for `n ≥ 16`
(reproduced from `Gdbh.PathCZChoiceConcrete.singlePowerLogZBound_zChoice₀`)
which gives `(log(Nat.sqrt n))^2 ≥ (log n)^2/16`, hence
`pairedBrunFactor(Nat.sqrt n) ≤ C/(log(Nat.sqrt n))^2 ≤ 16·C/(log n)^2`. -/

/-- Auxiliary: for `n ≥ 4`, `Nat.sqrt n ≥ 2`. -/
private lemma sqrt_ge_two_of_ge_four {n : ℕ} (h : 4 ≤ n) :
    2 ≤ Nat.sqrt n :=
  Nat.le_sqrt.mpr (by omega : 2 * 2 ≤ n)

/-- Auxiliary: for `n ≥ 4`, `n < 4 · (Nat.sqrt n)^2`. -/
private lemma four_sq_sqrt_gt {n : ℕ} (hn : 4 ≤ n) :
    n < 4 * (Nat.sqrt n) * (Nat.sqrt n) := by
  have h2 : 2 ≤ Nat.sqrt n := sqrt_ge_two_of_ge_four hn
  have hSucc : Nat.sqrt n + 1 ≤ 2 * Nat.sqrt n := by omega
  have hN_lt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have hSq : (Nat.sqrt n + 1) * (Nat.sqrt n + 1)
      ≤ (2 * Nat.sqrt n) * (2 * Nat.sqrt n) :=
    Nat.mul_le_mul hSucc hSucc
  have : n < (2 * Nat.sqrt n) * (2 * Nat.sqrt n) := lt_of_lt_of_le hN_lt hSq
  have heq : (2 * Nat.sqrt n) * (2 * Nat.sqrt n)
      = 4 * (Nat.sqrt n) * (Nat.sqrt n) := by ring
  rw [heq] at this
  exact this

/-- Auxiliary: for `n ≥ 16`, `log(Nat.sqrt n) ≥ (log n)/4`. -/
private lemma log_sqrt_ge_quarter_log {n : ℕ} (hn : 16 ≤ n) :
    Real.log (n : ℝ) / 4 ≤ Real.log ((Nat.sqrt n : ℕ) : ℝ) := by
  have hN16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN4 : 4 ≤ n := by omega
  have hN4r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN4
  have hN_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hN_gt1 : (1 : ℝ) < (n : ℝ) := by linarith
  have hlogN_pos : 0 < Real.log (n : ℝ) := Real.log_pos hN_gt1
  have h_log16 : Real.log (16 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hN16
  have h_log16_eq : Real.log (16 : ℝ) = 2 * Real.log (4 : ℝ) := by
    have : (16 : ℝ) = (4 : ℝ)^2 := by norm_num
    rw [this, Real.log_pow]; ring
  have h_log4_half : Real.log (4 : ℝ) ≤ Real.log (n : ℝ) / 2 := by
    have := h_log16; rw [h_log16_eq] at this; linarith
  have hsqrt_ge2 : 2 ≤ Nat.sqrt n := sqrt_ge_two_of_ge_four hN4
  have hsqrt_ge2_r : (2 : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hsqrt_ge2
  have hsqrt_pos : (0 : ℝ) < ((Nat.sqrt n : ℕ) : ℝ) := by linarith
  have h_core_nat : n < 4 * (Nat.sqrt n) * (Nat.sqrt n) := four_sq_sqrt_gt hN4
  have h_core_r : (n : ℝ) < 4 * ((Nat.sqrt n : ℕ) : ℝ) * ((Nat.sqrt n : ℕ) : ℝ) := by
    have := h_core_nat
    have hcast : ((4 * (Nat.sqrt n) * (Nat.sqrt n) : ℕ) : ℝ)
        = 4 * ((Nat.sqrt n : ℕ) : ℝ) * ((Nat.sqrt n : ℕ) : ℝ) := by
      push_cast; ring
    exact_mod_cast this
  have h4sqsq_pos :
      (0 : ℝ) < 4 * ((Nat.sqrt n : ℕ) : ℝ) * ((Nat.sqrt n : ℕ) : ℝ) := by
    have : (0 : ℝ) < 4 * ((Nat.sqrt n : ℕ) : ℝ) := by linarith
    exact mul_pos this hsqrt_pos
  have h_logN_le : Real.log (n : ℝ)
      ≤ Real.log (4 * ((Nat.sqrt n : ℕ) : ℝ) * ((Nat.sqrt n : ℕ) : ℝ)) :=
    Real.log_le_log hN_pos (le_of_lt h_core_r)
  have h_log_rhs :
      Real.log (4 * ((Nat.sqrt n : ℕ) : ℝ) * ((Nat.sqrt n : ℕ) : ℝ))
        = Real.log 4 + 2 * Real.log ((Nat.sqrt n : ℕ) : ℝ) := by
    have h4_pos : (0 : ℝ) < 4 := by norm_num
    have h4s_pos : (0 : ℝ) < 4 * ((Nat.sqrt n : ℕ) : ℝ) := by linarith
    rw [Real.log_mul (ne_of_gt h4s_pos) (ne_of_gt hsqrt_pos),
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hsqrt_pos)]
    ring
  rw [h_log_rhs] at h_logN_le
  have h_diff : Real.log (n : ℝ) - Real.log 4
      ≤ 2 * Real.log ((Nat.sqrt n : ℕ) : ℝ) := by linarith
  have h_half : Real.log (n : ℝ) / 2 ≤ 2 * Real.log ((Nat.sqrt n : ℕ) : ℝ) := by
    linarith
  linarith

/-- **Reduction of `MertensPairedProductBound pairedBrunFactor Nat.sqrt`
to `PairedBrunMertensThirdGap`.**

Assuming `pairedBrunFactor z ≤ C/(log z)²` (for `z ≥ z₀`), we obtain
`pairedBrunFactor(Nat.sqrt n) ≤ C₃/(log n)²` (for `n ≥ max(16, z₀²)`,
`n ≥ 2`), with `C₃ = ⌈16·C⌉ + 1`. -/
theorem mertensPairedProductBound_pairedBrunFactor_Nat_sqrt_of_gap
    (hGap : PairedBrunMertensThirdGap) :
    MertensPairedProductBound pairedBrunFactor Nat.sqrt := by
  obtain ⟨C, z₀, hCpos, hGapBound⟩ := hGap
  -- Pick `C₃ := Nat.ceil (16 * C) + 1`.
  set C₃ : ℕ := Nat.ceil (16 * C) + 1 with hC₃_def
  -- Pick `N₀ := max 16 (z₀ * z₀ + 1)` so that `Nat.sqrt n ≥ z₀` for `n ≥ N₀`.
  set N₀ : ℕ := max 16 (z₀ * z₀ + 1) with hN₀_def
  refine ⟨C₃, N₀, ?_, ?_⟩
  · -- `0 < C₃`.
    rw [hC₃_def]
    exact Nat.succ_pos _
  · intro n hN hN2
    have hN16 : 16 ≤ n := le_trans (le_max_left _ _) hN
    have hNsq : z₀ * z₀ + 1 ≤ n := le_trans (le_max_right _ _) hN
    have hNz₀ : z₀ * z₀ < n := by omega
    -- Step A: `Nat.sqrt n ≥ z₀`, so the gap applies at `z := Nat.sqrt n`.
    have hsqrt_ge_z₀ : z₀ ≤ Nat.sqrt n := by
      have : z₀ * z₀ ≤ n := by omega
      exact Nat.le_sqrt.mpr this
    have hMertensSqrt : pairedBrunFactor (Nat.sqrt n)
        ≤ C / (Real.log ((Nat.sqrt n : ℕ) : ℝ))^2 :=
      hGapBound (Nat.sqrt n) hsqrt_ge_z₀
    -- Step B: `log(Nat.sqrt n) ≥ (log n)/4`, so `(log(Nat.sqrt n))^2 ≥ (log n)^2/16`.
    have hlog_sqrt_ge : Real.log (n : ℝ) / 4
        ≤ Real.log ((Nat.sqrt n : ℕ) : ℝ) :=
      log_sqrt_ge_quarter_log hN16
    have hN_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hN2
    have hlogN_pos : 0 < Real.log (n : ℝ) := Real.log_pos hN_gt1
    have hlogN4_pos : 0 < Real.log (n : ℝ) / 4 := by linarith
    have hlog_sqrt_pos : 0 < Real.log ((Nat.sqrt n : ℕ) : ℝ) := by
      linarith
    have hlog_sqrt_sq_ge :
        (Real.log (n : ℝ) / 4)^2 ≤ (Real.log ((Nat.sqrt n : ℕ) : ℝ))^2 := by
      have hnn : 0 ≤ Real.log (n : ℝ) / 4 := le_of_lt hlogN4_pos
      exact pow_le_pow_left₀ hnn hlog_sqrt_ge 2
    -- Step C: combine `pairedBrunFactor(√n) ≤ C/(log √n)² ≤ C/((log n)/4)² = 16C/(log n)²`.
    have hlog_sqrt_sq_pos : 0 < (Real.log ((Nat.sqrt n : ℕ) : ℝ))^2 := by positivity
    have hlogN4_sq_pos : 0 < (Real.log (n : ℝ) / 4)^2 := by positivity
    have h_div_le :
        C / (Real.log ((Nat.sqrt n : ℕ) : ℝ))^2
          ≤ C / (Real.log (n : ℝ) / 4)^2 := by
      exact div_le_div_of_nonneg_left (le_of_lt hCpos) hlogN4_sq_pos
        hlog_sqrt_sq_ge
    have hBF_le : pairedBrunFactor (Nat.sqrt n)
        ≤ C / (Real.log (n : ℝ) / 4)^2 :=
      le_trans hMertensSqrt h_div_le
    -- `C / ((log n)/4)^2 = 16·C / (log n)^2`.
    have hlogN_sq_pos : 0 < (Real.log (n : ℝ))^2 := by positivity
    have h_alg : C / (Real.log (n : ℝ) / 4)^2 = 16 * C / (Real.log (n : ℝ))^2 := by
      have hne : (Real.log (n : ℝ))^2 ≠ 0 := ne_of_gt hlogN_sq_pos
      field_simp
      ring
    rw [h_alg] at hBF_le
    -- Step D: `16 * C ≤ C₃` (since `C₃ = ⌈16C⌉ + 1 ≥ 16C + 1 > 16C`).
    have h16C_le_C₃ : 16 * C ≤ (C₃ : ℝ) := by
      have h_ceil_ge : 16 * C ≤ (Nat.ceil (16 * C) : ℝ) := Nat.le_ceil _
      have h_C₃_eq : (C₃ : ℝ) = (Nat.ceil (16 * C) : ℝ) + 1 := by
        rw [hC₃_def]; push_cast; ring
      linarith
    -- Hence `16·C / (log n)^2 ≤ C₃ / (log n)^2`.
    have h_final : 16 * C / (Real.log (n : ℝ))^2
        ≤ (C₃ : ℝ) / (Real.log (n : ℝ))^2 :=
      div_le_div_of_nonneg_right h16C_le_C₃ (le_of_lt hlogN_sq_pos)
    -- Wait: that's wrong direction; we need numerator monotonicity, not denominator.
    -- Use `div_le_div_of_le_left` ... actually we want `a ≤ b → a/x ≤ b/x` for `x > 0`.
    -- That's `div_le_div_of_nonneg_right` *if* the second argument is the denominator nonneg.
    -- Actually in mathlib: `div_le_div_of_nonneg_right : a ≤ b → 0 ≤ c → a/c ≤ b/c`?
    -- Hmm, let me just chain via linarith.
    linarith

/-! ## Section 5 — The new named gap Prop

We define `BrunGoldbachPairedMainTerm` as the pinned-triple
specialisation of `BrunGoldbachMainTerm`.  Per the P13-T1 catch this
Prop is *conditionally false* (given `PairedBrunMertensThirdGap`), but
we record it as a named handle so that downstream code can document the
infeasibility of the pinned-zero closure precisely. -/

/-- **New named open Prop (P13-T1).**

`BrunGoldbachPairedMainTerm` is the *coordinated*-form sub-Prop
`BrunGoldbachMainTerm pairedBrunFactor (fun _ _ => 0)`.

**Status.**  Conditionally false under the open Prop
`PairedBrunMertensThirdGap` (see
`pairedBrunMertensThirdGap_disproves_brunGoldbachMainTerm_zero`).  It
is exposed as a named Prop *only* to document the precise
incompatibility of the pinned triple `(pairedBrunFactor, 0, Nat.sqrt)`;
the honest refactor uses the worst-case reservoir `B(n, z) := n` in
place of `0`.

It is *not vacuously true* (it would make the asymptotic claim
`goldbachSiftedPair n z ≤ C·n·pairedBrunFactor(z)`, which fails at the
explicit witness `n = 2`, `z` large).
It is *not vacuously false* either: at `z = 0`, `pairedBrunFactor 0 =
∏ p ∈ ∅, ... = 1`, and `goldbachSiftedPair n 0 ≤ n`, so the bound
`goldbachSiftedPair n 0 ≤ C · n · 1` holds with `C = 1`; the falsity is
only asymptotic. -/
def BrunGoldbachPairedMainTerm : Prop :=
  BrunGoldbachMainTerm pairedBrunFactor (fun _ _ => (0 : ℝ))

/-- The conditional disproof, re-exported at the named-Prop layer. -/
theorem brunGoldbachPairedMainTerm_false_of_gap
    (h : PairedBrunMertensThirdGap) :
    ¬ BrunGoldbachPairedMainTerm :=
  pairedBrunMertensThirdGap_disproves_brunGoldbachMainTerm_zero h

/-! ## Section 6 — Coordinated assembly theorem

We assemble `GoldbachRepresentationBound` from the *named* inputs:

* `BrunGoldbachPairedMainTerm` — the (conditionally false) main-term
  sub-Prop at the pinned triple;
* `MertensFirstTheoremBound` — Mertens' 1st theorem;
* `AbelInversionMertensSecondFromFirst` — the Abel-summation arrow;
* the elementary small-sieve side condition for `Nat.sqrt`.

The first input is the "infeasible" piece — the assembly cannot close
without it, and *every* witness for it is contradictory with
`PairedBrunMertensThirdGap`.  The assembly is therefore *honest* about
the trade-off: either keep the zero reservoir (and contradict the
Mertens gap, ruling out closure via the pinned triple), or replace it
with a non-zero reservoir (the worst-case `B(n, z) := n`, closed
axiom-cleanly downstream). -/

/-- **Coordinated assembly theorem.**

Given the coordinated inputs

* `hMain : BrunGoldbachPairedMainTerm` — the pinned main-term sub-Prop;
* `hM1 : MertensFirstTheoremBound` — Mertens' 1st theorem;
* `hAbel : AbelInversionMertensSecondFromFirst` — Abel-summation arrow;
* `hSmall` — the elementary small-sieve side condition for `Nat.sqrt`,
  `∃ N₁, ∀ n ≥ N₁, n ≥ 2 → 2 · (√n + 1) ≤ n / (log n)²`;

the original named open Prop `GoldbachRepresentationBound` holds.

The proof composes:

1. `hM1, hAbel → MertensSecondLowerBoundOdd → PairedBrunMertensThirdGap`
   (P9-T3 and P11-T1 chain);
2. `PairedBrunMertensThirdGap → MertensPairedProductBound pairedBrunFactor
   Nat.sqrt` (this file);
3. `brunGoldbachErrorTerm_zero_Nat_sqrt` — trivial zero reservoir
   closure (P11-T2);
4. The P10-T2 assembly
   `goldbachRepresentationBound_of_brunComponents`. -/
theorem goldbachRepresentationBound_of_coordinated
    (hMain : BrunGoldbachPairedMainTerm)
    (hM1 : MertensFirstTheoremBound)
    (hAbel : AbelInversionMertensSecondFromFirst)
    (hSmall : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → 2 ≤ n →
                2 * ((Nat.sqrt n : ℝ) + 1)
                  ≤ (n : ℝ) / (Real.log (n : ℝ))^2) :
    GoldbachRepresentationBound := by
  -- Step 1: M1 + Abel ⇒ PairedBrunMertensThirdGap.
  have hGap : PairedBrunMertensThirdGap :=
    pairedBrunMertensThirdGap_of_first_and_abel hM1 hAbel
  -- Step 2: Mertens sub-Prop closes for the pinned triple.
  have hMert : MertensPairedProductBound pairedBrunFactor Nat.sqrt :=
    mertensPairedProductBound_pairedBrunFactor_Nat_sqrt_of_gap hGap
  -- Step 3: Error sub-Prop closes for the pinned triple (trivial).
  have hErr : BrunGoldbachErrorTerm (fun _ _ => (0 : ℝ)) Nat.sqrt :=
    brunGoldbachErrorTerm_zero_Nat_sqrt
  -- Step 4: Apply P10-T2 assembly.
  exact goldbachRepresentationBound_of_brunComponents
    pairedBrunFactor (fun _ _ => (0 : ℝ)) Nat.sqrt
    hMain hErr hMert hSmall

/-- **Pure existential closer (coordinated form).**  Same as
`goldbachRepresentationBound_of_coordinated`, but packaged as a single
existential. -/
theorem goldbachRepresentationBound_of_coordinated_exists
    (h : BrunGoldbachPairedMainTerm ∧ MertensFirstTheoremBound
          ∧ AbelInversionMertensSecondFromFirst
          ∧ (∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → 2 ≤ n →
                2 * ((Nat.sqrt n : ℝ) + 1)
                  ≤ (n : ℝ) / (Real.log (n : ℝ))^2)) :
    GoldbachRepresentationBound :=
  goldbachRepresentationBound_of_coordinated h.1 h.2.1 h.2.2.1 h.2.2.2

/-! ## Section 7 — Honest refactor (`B := fun n _ => (n : ℝ)`)

We provide the axiom-clean closure of `BrunGoldbachMainTerm
pairedBrunFactor (fun n _ => (n : ℝ))` — the *honest* refactor that
restores closability of the main-term piece at the cost of forcing the
error reservoir to absorb the analytic content.  This is the
Goldbach-side analogue of
`Gdbh.PathCBrunMainProof.brunMainTerm_pairedBrunFactor_worstCaseError`. -/

/-- **Honest refactor of the main-term sub-Prop.**  With `M :=
pairedBrunFactor` and the worst-case error reservoir `B(n, z) := n`,
the paired-sift main-term inequality

```
goldbachSiftedPair n z  ≤  1 · n · pairedBrunFactor z  +  n
```

holds axiom-cleanly, because `goldbachSiftedPair n z ≤ n` is the
trivial cardinal bound and `1 · n · pairedBrunFactor z ≥ 0`.

Compared to `BrunGoldbachPairedMainTerm` (the pinned-zero version),
this refactored sub-Prop is *true* — but the price is that the
companion `BrunGoldbachErrorTerm B Nat.sqrt` for `B(n, z) := n` is
**no longer trivially true**: it now demands `n ≤ C₂·n/(log n)²`,
which fails for `n ≥ 3`.  So one closes the main-term sub-Prop here
and shifts the analytic gap onto the *honest* Brun combinatorial
estimate at the error layer. -/
theorem brunGoldbachMainTerm_pairedBrunFactor_worstCaseError :
    BrunGoldbachMainTerm pairedBrunFactor (fun n _ => (n : ℝ)) := by
  refine ⟨pairedBrunFactor_isBrunMainTermFactor, 1, by norm_num, ?_⟩
  intro n z _hn
  have hSift : (goldbachSiftedPair n z : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast goldbachSiftedPair_le n z
  have hMnn : 0 ≤ pairedBrunFactor z := le_of_lt (pairedBrunFactor_pos z)
  have hNnn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_extra : 0 ≤ 1 * (n : ℝ) * pairedBrunFactor z :=
    mul_nonneg (by linarith) hMnn
  linarith

/-! ## Section 8 — P13-T1 summary -/

/-- **P13-T1 summary, in proof form.**

**Mission**: attempt coordinated closure of the three Brun-Goldbach
sub-Props from `Gdbh/PathC_GoldbachRBound.lean` by pinning a *single*
consistent triple `(M, B, zChoice) = (pairedBrunFactor, fun _ _ => 0,
Nat.sqrt)`.

**Outcome (honest)**:

1. `BrunGoldbachMainTerm pairedBrunFactor (fun _ _ => 0)` is
   *conditionally false* under `PairedBrunMertensThirdGap`
   (witness `n = 2` with `goldbachSiftedPair 2 z = 1` and
   `pairedBrunFactor z → 0`).  This is the same catch as
   `Gdbh.PathCBrunMainProof.pairedBrunMertensThirdGap_disproves_brunMain`
   at the single-sift layer, transplanted to the paired sift.

2. `BrunGoldbachErrorTerm (fun _ _ => 0) Nat.sqrt` is *trivially true*
   (reuses `brunGoldbachErrorTerm_concrete` from P11-T2).

3. `MertensPairedProductBound pairedBrunFactor Nat.sqrt` *reduces*
   axiom-cleanly to `PairedBrunMertensThirdGap` via
   `pairedBrunFactor(Nat.sqrt n) ≤ C/(log(Nat.sqrt n))² ≤ 16·C/(log n)²`.
   The named gap chains: `MertensFirstTheoremBound +
   AbelInversionMertensSecondFromFirst → MertensSecondLowerBoundOdd →
   PairedBrunMertensThirdGap`.

**Atomic gap structure**:

* The pinned triple *cannot* close `GoldbachRepresentationBound` because
  its main-term sub-Prop is conditionally false.
* The honest refactor replaces the zero reservoir with
  `B(n, z) := n` (axiom-clean closure of the main term — see
  `brunGoldbachMainTerm_pairedBrunFactor_worstCaseError`) and shifts the
  analytic content to the *error layer*, where the Brun combinatorial
  estimate `(π(z))^k/k!` must be honestly bounded.
* The *truly atomic* mathlib-level gap remains
  `MertensFirstTheoremBound` (chained through P11-T1 and P9-T3 to
  `PairedBrunMertensThirdGap`) plus an honest Brun combinatorial-error
  closure with a non-zero reservoir.

**Coordinated assembly**:

* `goldbachRepresentationBound_of_coordinated` — packages the four
  named inputs (the conditionally-false `BrunGoldbachPairedMainTerm`,
  `MertensFirstTheoremBound`, `AbelInversionMertensSecondFromFirst`,
  and the small-sieve side condition for `Nat.sqrt`) into
  `GoldbachRepresentationBound`.

All deliverables are axiom-clean: only `Classical.choice`, `Quot.sound`,
`propext` are transitively used. -/
theorem pathC_p13_t1_summary : True := trivial

end PathCBrunGoldbachComposition
end Gdbh
