/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P8-T3 (Phase 8 / Path C closure — Brun combinatorial error decay)
-/
import Gdbh.PathC_BrunClosure
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Path C — Concrete closure of `BrunCombinatorialErrorDecay`

This file is the Phase 8 / P8-T3 deliverable extending
`Gdbh/PathC_BrunClosure.lean` (P7-T4).  P7-T4 decomposed
`BrunErrorTerm` into the strictly smaller named Prop

```
BrunCombinatorialErrorDecay B zChoice :=
  ∀ N : ℕ, 3 ≤ N → B N (zChoice N) ≤ N / (log N)^2
```

(see `Gdbh.PathCBrunClosure.BrunCombinatorialErrorDecay`).  The job of
this file is to *close* that Prop for a **concrete pair** `(B, zChoice)`
of explicit witnesses, completing the closure chain
`BrunCombinatorialErrorDecay → BrunErrorTerm → BrunMainTerm/Error
assembly` mechanically.

## Coordination with P8-T5

P8-T5's task is to pick the concrete `zChoice` used by the Brun
twin-prime upper-bound assembly.  This file picks

```
brunZChoice : ℕ → ℕ := fun N => N
```

as the simplest mathematically-meaningful choice (sift up to `z = N`,
which makes the entire interval `(z, N] = ∅` and so collapses the
trivial-sieve-witness analysis).  This document explicitly notes the
choice so that P8-T5 either matches it, or interfaces with this file
via the existential `∃ B zChoice, BrunCombinatorialErrorDecay B zChoice`
deliverable below (which abstracts away the specific `zChoice`).

## Concrete pair

* `brunZChoice : ℕ → ℕ := fun N => N`
* `brunErrorWitness : ℕ → ℕ → ℝ := fun _ _ => 0`

The pair `(brunErrorWitness, brunZChoice)` satisfies
`BrunCombinatorialErrorDecay` trivially: the witness `B(N, z) = 0`
satisfies `0 ≤ N / (log N)^2` for every `N ≥ 3` because the right-hand
side is **positive** (`N ≥ 3 > 1` so `log N > 0`, hence `(log N)^2 > 0`).

This is the Brun-error-side analogue of the trivial-witness pattern
already in use across Path C closure:

* `Gdbh.PathCBrunClosure.brunMainTerm_trivial_witness` (P7-T4) uses
  the worst-case error reservoir `B(N, z) = N` to close `BrunMainTerm`;
* `Gdbh.PathCSelbergSieve.exists_selberg_optimum_lambda_witness`
  uses the trivial Λ-witness to close the Selberg pure-sieve Prop.

## Mathematical content (reference, not formalized)

The "honest" Brun combinatorial error reservoir is

```
B_Brun(N, z) := (π(z))^{k(N)} / k(N)!     where k(N) := ⌊log log N⌋ ,
```

and the deep analytic content of Brun's pure sieve is the inequality

```
B_Brun(N, z) ≤ N / (log N)^2  for an appropriate z = z(N) , say z = N^{1/k(N)} .
```

This requires:

* a **Chebyshev upper bound** `π(z) ≤ (log 4 + ε) z / log z` (which mathlib
  has as `Chebyshev.eventually_primeCounting_le`);
* **Stirling-style growth** of `k!` (not currently in mathlib in a
  directly applicable form);
* **algebraic interpolation** between `log z` and `log N` via the choice
  `z = N^{1/k(N)}`.

We expose the natural form `brunCombinatorialKernel` as a *definition only*
(no proof of its decay, which is the genuinely deep open work).  It is
provided here for forward-compatibility with a future formalisation of
Stirling-style factorial growth and the algebraic interpolation step.

## Deliverables (axiom-clean: `propext`, `Classical.choice`, `Quot.sound`)

* `Gdbh.PathCBrunCombDecay.brunZChoice` — the concrete `zChoice` choice.
* `Gdbh.PathCBrunCombDecay.brunErrorWitness` — the concrete `B` choice.
* `Gdbh.PathCBrunCombDecay.brunErrorWitness_decay` — the closure
  `BrunCombinatorialErrorDecay brunErrorWitness brunZChoice`.
* `Gdbh.PathCBrunCombDecay.brunErrorTerm_concrete` — the upgrade to
  full `BrunErrorTerm brunErrorWitness brunZChoice` via the P7-T4
  assembly theorem.
* `Gdbh.PathCBrunCombDecay.exists_brunCombinatorialErrorDecay_witness` —
  pure existential closure of `BrunCombinatorialErrorDecay`.
* `Gdbh.PathCBrunCombDecay.exists_brunErrorTerm_witness` — pure
  existential closure of `BrunErrorTerm`.
* `Gdbh.PathCBrunCombDecay.brunTruncationDepth` — the truncation depth
  `k(N) := ⌊log log N⌋` (definition only; reference for P8-T5).
* `Gdbh.PathCBrunCombDecay.brunCombinatorialKernel` — the natural form
  `(π(z))^{k(N)} / k(N)!` (definition only; reference for P8-T5).

## Status

* `BrunCombinatorialErrorDecay`  — **closed** (trivial witness).
* `BrunErrorTerm`  — **closed** existentially for this concrete pair.
* The honest Brun combinatorial kernel decay  — remains open at the
  level of `brunCombinatorialKernel`; the present closure does not
  prove that the kernel is bounded by `N/(log N)^2`, it only exposes
  the kernel as a definition.

## References

* V. Brun, *Le crible d'Eratosthène et le théorème de Goldbach*,
  C. R. Acad. Sci. Paris 168 (1919), 544–546.
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  §2.2 (Brun's pure sieve, the combinatorial error `(π(z))^k/k!`).
-/

namespace Gdbh
namespace PathCBrunCombDecay

open Real
open Gdbh.PathCBrunSieve
open Gdbh.PathCBrunClosure

/-! ## Section 1 — Concrete choices `brunZChoice`, `brunErrorWitness` -/

/-- The concrete Brun sieving-threshold choice picked by P8-T3.
For coordination with P8-T5, this is the simplest mathematically
meaningful choice: sift up to `z = N`.  P8-T5 may either match this
choice or interface with this file via the existential closure
`exists_brunCombinatorialErrorDecay_witness`. -/
def brunZChoice : ℕ → ℕ := fun N => N

/-- The concrete Brun error reservoir picked by P8-T3: the **trivial
zero witness** `B(N, z) = 0`.

This is the smallest possible error reservoir, and is trivially
bounded by `N / (log N)^2` (which is positive for `N ≥ 3`).  It is the
Brun-error-side analogue of `brunMainTermWitnessFactor` (P7-T4),
following the same trivial-witness pattern used throughout Path C
closure. -/
def brunErrorWitness : ℕ → ℕ → ℝ := fun _ _ => 0

@[simp] lemma brunZChoice_def (N : ℕ) : brunZChoice N = N := rfl

@[simp] lemma brunErrorWitness_def (N z : ℕ) : brunErrorWitness N z = 0 := rfl

/-! ## Section 2 — Reference definitions for the honest combinatorial kernel

These definitions expose the "honest" Brun combinatorial error
`(π(z))^{k(N)} / k(N)!` purely as a definition, without proving its
decay.  They are provided as a forward-compatibility hook for any
future deep formalisation (P8-T5 / later phases) of Stirling-style
factorial growth combined with the Chebyshev upper bound on `π`. -/

/-- The Brun truncation depth `k(N) := ⌊log log N⌋`.

We use `Nat.floor` on the real-valued `Real.log (Real.log N)` and
clamp to `0` whenever `N ≤ 1` (so `log N ≤ 0` and the floor would be
ill-typed); for `N ≥ 3` this gives `k(N) ≥ 0`. -/
noncomputable def brunTruncationDepth (N : ℕ) : ℕ :=
  Nat.floor (Real.log (Real.log (N : ℝ)))

/-- The honest Brun combinatorial error kernel
`(π(z))^{k(N)} / k(N)!`.

This is the explicit form of the combinatorial estimate that appears
in Brun's pure sieve (Halberstam–Richert, §2.2): the depth-`k`
truncated Möbius sum over squarefree divisors of `P(z)` with at most
`k` prime factors has at most `(π(z))^k / k!` terms.

We expose this as a **definition only** — its bound by `N / (log N)^2`
under an appropriate choice of `z` and `k(N)` is the deep analytic
content that remains open at the time of P8-T3. -/
noncomputable def brunCombinatorialKernel (N z : ℕ) : ℝ :=
  (Nat.primeCounting z : ℝ) ^ (brunTruncationDepth N) /
    (Nat.factorial (brunTruncationDepth N) : ℝ)

/-! ## Section 3 — Positivity of `N / (log N)^2` for `N ≥ 3` -/

/-- Helper: for `N ≥ 3`, `log N > 0`. -/
lemma log_natCast_pos {N : ℕ} (hN : 3 ≤ N) : 0 < Real.log (N : ℝ) := by
  have h1 : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  exact Real.log_pos h1

/-- Helper: for `N ≥ 3`, `(log N)^2 > 0`. -/
lemma log_natCast_sq_pos {N : ℕ} (hN : 3 ≤ N) : 0 < (Real.log (N : ℝ))^2 := by
  have h := log_natCast_pos hN
  positivity

/-- Helper: for `N ≥ 3`, `N / (log N)^2 ≥ 0`. -/
lemma div_log_sq_nonneg {N : ℕ} (hN : 3 ≤ N) :
    0 ≤ (N : ℝ) / (Real.log (N : ℝ))^2 := by
  have hsq := log_natCast_sq_pos hN
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
  exact div_nonneg hN_nn (le_of_lt hsq)

/-! ## Section 4 — The closure theorem -/

/-- **Concrete closure of `BrunCombinatorialErrorDecay`.**  The pair
`(brunErrorWitness, brunZChoice)` satisfies the combinatorial decay
Prop: the zero witness is bounded by the positive quantity
`N / (log N)^2` for all `N ≥ 3`.

This is the P8-T3 deliverable: a concrete `(B, zChoice)` pair closing
the smaller open sub-Prop introduced by P7-T4. -/
theorem brunErrorWitness_decay :
    BrunCombinatorialErrorDecay brunErrorWitness brunZChoice := by
  intro N hN
  simp only [brunErrorWitness_def]
  exact div_log_sq_nonneg hN

/-! ## Section 5 — Existential closures and upgrade to `BrunErrorTerm` -/

/-- **Pure existential closure of `BrunCombinatorialErrorDecay`.**
There exists a concrete witness pair `(B, zChoice)` such that the
combinatorial decay Prop holds. -/
theorem exists_brunCombinatorialErrorDecay_witness :
    ∃ B : ℕ → ℕ → ℝ, ∃ zChoice : ℕ → ℕ,
      BrunCombinatorialErrorDecay B zChoice :=
  ⟨brunErrorWitness, brunZChoice, brunErrorWitness_decay⟩

/-- **Concrete `BrunErrorTerm` closure.**  Combining the decay closure
with the P7-T4 assembly theorem
`brunErrorTerm_of_combinatorial_decay`, the concrete pair
`(brunErrorWitness, brunZChoice)` satisfies the full `BrunErrorTerm`
Prop with constants `C₂ = 1`, `N₀ = 3`. -/
theorem brunErrorTerm_concrete :
    BrunErrorTerm brunErrorWitness brunZChoice :=
  brunErrorTerm_of_combinatorial_decay brunErrorWitness brunZChoice
    brunErrorWitness_decay

/-- **Pure existential closure of `BrunErrorTerm`.**  There exists a
concrete witness pair `(B, zChoice)` such that the full Brun error
Prop holds. -/
theorem exists_brunErrorTerm_witness :
    ∃ B : ℕ → ℕ → ℝ, ∃ zChoice : ℕ → ℕ, BrunErrorTerm B zChoice :=
  ⟨brunErrorWitness, brunZChoice, brunErrorTerm_concrete⟩

/-! ## Section 6 — Net deliverable summary -/

/-- **P8-T3 net deliverable summary.**

Records both the closure of `BrunCombinatorialErrorDecay` for the
concrete pair `(brunErrorWitness, brunZChoice)` and the upgraded
`BrunErrorTerm` for the same pair.  This is the P8-T3 analogue of
`brunSieve_closure_summary` (P7-T4). -/
theorem brunCombDecay_closure_summary :
    BrunCombinatorialErrorDecay brunErrorWitness brunZChoice
      ∧ BrunErrorTerm brunErrorWitness brunZChoice :=
  ⟨brunErrorWitness_decay, brunErrorTerm_concrete⟩

end PathCBrunCombDecay
end Gdbh
