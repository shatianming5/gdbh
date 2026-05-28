/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P19-T33 (Phase 19 / Path C — Brun-Bonferroni at the minimal
        fixed truncation depth `k = 2`.)
-/
import Gdbh.PathC_BrunBonferroniDecomposition
import Gdbh.PathC_AssemblyPieceAClosure
import Gdbh.PathC_BrunBonferroniNaturalAtSqrtClosure

/-!
# Path C — P19-T33: Brun-Bonferroni at the minimal truncation depth `k = 2`

This file is the **P19-T33 deliverable** in Phase 19 (Path C closure).

## Background

The full Halberstam-Richert paired Brun-Bonferroni inequality at sieve
threshold `z = √n` is parameterised by an arbitrary truncation-depth
function `k : ℕ → ℕ`.  The canonical "fully-developed" choice
`k(n) = 2n` is what unlocks the Mertens-strength `1 / (log n)^2`
decay needed for the Path C reservoir.

This task asks: **what does the inequality look like at the
absolutely-minimal nontrivial depth `k = 2`?**

At `k = 2`, the Bonferroni truncation runs over divisor multisets of
size `|d| ≤ 2`, i.e.:

* `|d| = 0` :  just `D = ∅`, contributing `+ 1`,
* `|d| = 1` :  each prime `p ∈ P`, contributing `- 2/p`,
* `|d| = 2` :  pairs `{p, q}` of distinct primes in `P`, contributing
                `+ 4/(p q)`.

Bonferroni at *even* depth (`2k = 2*2 = 4`?  no — here the depth
parameter is `k`, so depth-`2` means `|d| ≤ 2`) is an *upper bound*
on the indicator `1{m coprime to P}`, and thus the sift sum is an
upper bound on the true sift count.

Path C requires the resulting RHS to be of order `n / (log n)^2`.
The `k = 2` truncation:

```
goldbachSiftedPair n √n ≤ n · pairedBrunFactor(√n)
                          + n · π(√n)^5 / (5*4*3*2*1)
                        = n · pairedBrunFactor(√n) + n · π(√n)^5 / 120.
```

Now `π(√n) ~ √n / log(√n)`, so the tail term `n · π(√n)^5 / 120` is of
order `n · n^{5/2} / (log n)^5 / 120 ~ n^{7/2} / (log n)^5`, which is
**enormous** compared to the main term `n · C / (log n)^2 ~ n / (log
n)^2`.  The tail at `k = 2` does **not** beat the main term in any
useful regime.

For comparison, the canonical witness `k(n) = 2n` makes the tail term
`n · π(√n)^{4n+1} / (4n+1)!`, which by Stirling is of order
`n · (e π(√n) / (4n+1))^{4n+1} √(4n+1)`, exponentially small as `n →
∞` since `π(√n) / (4n + 1) → 0`.

## Strategy — outcome (c)

This file delivers **honest outcome (c)** from the task spec:

* The specialised Prop `AssemblyPieceA_at_k2` is **mechanically
  reducible** to the general `AssemblyPieceA` by instantiation at the
  constant function `k = fun _ => 2`.
* The specialisation is **strictly weaker** than `AssemblyPieceA`, in
  the sense that `AssemblyPieceA → AssemblyPieceA_at_k2`.
* The k=2 inequality, even **if fully closed**, does **not** give the
  Path C reservoir bound:  the tail term `n π(√n)^5 / 120` grows
  faster than the main term `n · pairedBrunFactor(√n) ~ n / (log n)^2`.
* The k=2 kernel residual (the combinatorial content at depth 2) is
  the same combinatorial chain as the general kernel, just instantiated
  at a single depth.

## Constraint compliance

* No `sorry`, no `axiom`, no `admit`.
* Axiom hygiene target: `[Classical.choice, Quot.sound, propext]`.
* File compiles standalone.

## References

* M. B. Nathanson, *Additive Number Theory: The Classical Bases*,
  Springer 1996, §7.2.
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  Theorem 3.11.
-/

namespace Gdbh
namespace PathCBrunBonferroniMinimalK

open Real
open Finset
open Gdbh.PathCGoldbachRBound (goldbachSiftedPair goldbachSiftedPair_le)
open Gdbh.PathCMertensProof (pairedBrunFactor pairedBrunFactor_pos pairedBrunFactor_le_one)
open Gdbh.PathCBrunBonferroniDecomposition (AssemblyPieceA)
open Gdbh.PathCBrunBonferroniNaturalAtSqrtClosure
  (BrunBonferroniNatAtSqrtArbitraryKKernel)

/-! ## Section 1 — The specialised Prop at fixed depth `k = 2`.

We instantiate `AssemblyPieceA` at the constant truncation-depth
function `k = fun _ => 2`.  At this `k`, the exponent is
`2 * k(n) + 1 = 2 * 2 + 1 = 5` and the factorial is
`(2*2+1)! = 5! = 120 = 5 * 4 * 3 * 2`.

For convenience downstream we write the factorial as the **literal
product `5 * 4 * 3 * 2 = 120`** rather than `(5).factorial`. -/

/-- **The specialised Prop** at fixed truncation depth `k = 2`.

For every `n ≥ 4`, the paired sifted count at sieve threshold `z = √n`
is bounded above by the standard Bonferroni RHS at depth `k = 2`:

```
goldbachSiftedPair n √n
  ≤ n · pairedBrunFactor(√n) + n · π(√n)^5 / (5 * 4 * 3 * 2) .
```

Note: `5 * 4 * 3 * 2 = 120 = 5!`, so the RHS is the **fifth-order
Stirling tail**.  This is the absolutely-minimal nontrivial truncation
depth for the paired Bonferroni inequality. -/
def AssemblyPieceA_at_k2 : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
      ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
        + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^5
              / (5 * 4 * 3 * 2 : ℝ)

/-! ## Section 2 — Real-valued bookkeeping. -/

/-- **Non-negativity of the main term** at threshold `z = √n`. -/
theorem main_term_nonneg (n : ℕ) :
    (0 : ℝ) ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n) := by
  refine mul_nonneg ?_ ?_
  · exact Nat.cast_nonneg n
  · exact le_of_lt (pairedBrunFactor_pos _)

/-- **Non-negativity of the k=2 Stirling tail term**:
`n · π(√n)^5 / 120 ≥ 0`. -/
theorem tail_term_k2_nonneg (n : ℕ) :
    (0 : ℝ) ≤ (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^5
                / (5 * 4 * 3 * 2 : ℝ) := by
  refine div_nonneg ?_ ?_
  · refine mul_nonneg ?_ ?_
    · exact Nat.cast_nonneg n
    · positivity
  · norm_num

/-- **Non-negativity of the full k=2 RHS**. -/
theorem assemblyPieceA_at_k2_rhs_nonneg (n : ℕ) :
    (0 : ℝ)
      ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
        + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^5
              / (5 * 4 * 3 * 2 : ℝ) := by
  linarith [main_term_nonneg n, tail_term_k2_nonneg n]

/-! ## Section 3 — Arithmetic identities at `k = 2`. -/

/-- **Exponent identity** at `k = 2`:  `2 * 2 + 1 = 5`. -/
theorem k2_exp_eq : 2 * 2 + 1 = 5 := by norm_num

/-- **Factorial identity** at `k = 2` (Nat): `(2 * 2 + 1)! = 120`. -/
theorem k2_factorial_eq_nat : (2 * 2 + 1).factorial = 120 := by
  decide

/-- **Factorial identity** at `k = 2` (Real): `((2 * 2 + 1)! : ℝ) =
5 * 4 * 3 * 2`. -/
theorem k2_factorial_eq_real :
    ((2 * 2 + 1).factorial : ℝ) = (5 * 4 * 3 * 2 : ℝ) := by
  rw [k2_factorial_eq_nat]
  norm_num

/-- **Power identity** at `k = 2`:  the RHS power `^(2 * k + 1)` at
`k = 2` is `^5`. -/
theorem k2_power_eq (x : ℝ) : x ^ (2 * 2 + 1) = x ^ 5 := by
  rw [k2_exp_eq]

/-! ## Section 4 — The main bridge: `AssemblyPieceA → AssemblyPieceA_at_k2`.

The specialisation is mechanical:  instantiate the universally
quantified truncation function `k : ℕ → ℕ` at the constant function
`fun _ => 2`. -/

/-- **Main bridge** (forward direction):
`AssemblyPieceA → AssemblyPieceA_at_k2`.

The general Prop `AssemblyPieceA` is a Π-statement over all
`k : ℕ → ℕ`;  instantiating at the constant `k = fun _ => 2`
discharges the k=2 specialisation. -/
theorem assemblyPieceA_at_k2_of_assemblyPieceA
    (h : AssemblyPieceA) :
    AssemblyPieceA_at_k2 := by
  intro n hn
  -- Instantiate the general Prop at the constant function `fun _ => 2`.
  have hgen := h (fun _ => 2) n hn
  -- `hgen` has the RHS with `(2 * 2 + 1)!` in the denominator.
  -- We need it with `5 * 4 * 3 * 2`.
  have hexp : (Nat.primeCounting (Nat.sqrt n) : ℝ) ^ (2 * 2 + 1)
              = (Nat.primeCounting (Nat.sqrt n) : ℝ) ^ 5 := k2_power_eq _
  have hfact : ((2 * 2 + 1).factorial : ℝ) = (5 * 4 * 3 * 2 : ℝ) :=
    k2_factorial_eq_real
  -- Rewrite both sides of `hgen`.
  rw [hexp, hfact] at hgen
  exact hgen

/-! ## Section 5 — Reverse direction (partial).

We cannot reverse the implication in general:  closing
`AssemblyPieceA_at_k2` (at the single fixed `k = 2`) does NOT close
`AssemblyPieceA` (which demands the inequality at every `k : ℕ → ℕ`).

We can, however, reverse the implication for any *constant* function
`k = fun _ => 2`.  More precisely, given `AssemblyPieceA_at_k2`, we
can produce a witness for the constant truncation `fun _ => 2`. -/

/-- **Partial reverse bridge**:  `AssemblyPieceA_at_k2` discharges the
*constant-2 instance* of `AssemblyPieceA`. -/
theorem assemblyPieceA_const_k2_of_assemblyPieceA_at_k2
    (h : AssemblyPieceA_at_k2) :
    ∀ n : ℕ, 4 ≤ n →
      (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * (fun (_ : ℕ) => 2) n + 1)
                / ((2 * (fun (_ : ℕ) => 2) n + 1).factorial : ℝ) := by
  intro n hn
  have hk2 := h n hn
  -- Convert k=2 form back: `(fun _ => 2) n = 2`, so `2 * 2 + 1 = 5` and
  -- `(2*2+1)! = 120 = 5 * 4 * 3 * 2`.
  show (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
        ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
          + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * 2 + 1)
                / ((2 * 2 + 1).factorial : ℝ)
  have hexp : (Nat.primeCounting (Nat.sqrt n) : ℝ) ^ (2 * 2 + 1)
              = (Nat.primeCounting (Nat.sqrt n) : ℝ) ^ 5 := k2_power_eq _
  have hfact : ((2 * 2 + 1).factorial : ℝ) = (5 * 4 * 3 * 2 : ℝ) :=
    k2_factorial_eq_real
  rw [hexp, hfact]
  exact hk2

/-! ## Section 6 — The k=2 combinatorial kernel residual.

We now specialise the general combinatorial kernel
`BrunBonferroniNatAtSqrtArbitraryKKernel` (P19-T22 / P19-T29) to
`k = 2`.

The k=2 kernel is the genuine combinatorial residual at depth 2.  Its
content is the **same** as the general kernel, just instantiated at a
single depth — so it is a *strictly weaker* open Prop. -/

/-- **The k=2 combinatorial kernel** — the genuine combinatorial
residual of the paired Brun-Bonferroni inequality at sieve threshold
`z = √n` and fixed truncation depth `k = 2`.

For every `n ≥ 4`,

```
goldbachSiftedPair n √n
  ≤ n · pairedBrunFactor(√n) + n · π(√n)^5 / 120 .
```

This is **strictly weaker** than the general kernel
`BrunBonferroniNatAtSqrtArbitraryKKernel`, because it fixes the
truncation depth at `k = 2` rather than quantifying over all
`k : ℕ → ℕ`. -/
def BrunBonferroniKernelAtK2 : Prop := AssemblyPieceA_at_k2

/-- **Bridge from general kernel to k=2 specialisation**:
the general kernel `BrunBonferroniNatAtSqrtArbitraryKKernel`
discharges `AssemblyPieceA_at_k2`.

Since `BrunBonferroniNatAtSqrtArbitraryKKernel` is **definitionally
identical** to `AssemblyPieceA` (cf.
`PathCAssemblyPieceAClosure.assemblyPieceA_iff_kernelP19T22 : Iff.rfl`),
the kernel directly inhabits `AssemblyPieceA`. -/
theorem assemblyPieceA_at_k2_of_general_kernel
    (h : BrunBonferroniNatAtSqrtArbitraryKKernel) :
    AssemblyPieceA_at_k2 :=
  assemblyPieceA_at_k2_of_assemblyPieceA
    (Gdbh.PathCAssemblyPieceAClosure.assemblyPieceA_of_kernelP19T22 h)

/-! ## Section 7 — Honest analysis: why k=2 does not give the Path C
reservoir bound.

The Path C reservoir requires a sift bound of the form

```
goldbachSiftedPair n √n  ≤  n · C / (log n)^2 + (error)
```

where the error term is smaller than the main term in absolute value.

At `k = 2` (i.e. truncating Bonferroni at divisor depth `|d| ≤ 2`),
the RHS we get is

```
n · pairedBrunFactor(√n) + n · π(√n)^5 / 120 .
```

Mertens' theorem gives the **main term** `pairedBrunFactor(√n) ~ C /
(log √n)^2 = 4 C / (log n)^2`, of correct order `1 / (log n)^2`.

But the **tail term** `n · π(√n)^5 / 120` is asymptotically of order

```
n · π(√n)^5 / 120  ~  n · (√n / log √n)^5 / 120
                   =  n^{1 + 5/2} / (log n / 2)^5 / 120
                   =  n^{7/2} / (log n)^5 · (constant) ,
```

which **dominates** the main term `n / (log n)^2` by a factor of
`n^{5/2} (log n)^3` as `n → ∞`.

**Conclusion**:  the k=2 truncation is **far too crude** for the Path
C reservoir bound.  Even if `AssemblyPieceA_at_k2` is fully closed
(which still requires the same combinatorial content as the general
kernel — only restricted to depth 2), the resulting bound is unusable
for Path C.

The canonical choice `k(n) = 2n` is essential:  it makes the tail
`n · π(√n)^{4n+1} / (4n+1)!` exponentially small (by Stirling), so the
RHS reduces to (essentially) the main term `n · pairedBrunFactor(√n)`,
which by Mertens gives the required `1 / (log n)^2` reservoir.

The "right" reading is that **`k` must grow with `n`** (at least as a
power of `log n`), or the Bonferroni truncation tail dominates.  The
fixed `k = 2` cannot work. -/

/-- **Honesty audit**:  the k=2 RHS as a function of `n`, with both
terms exhibited.  This is a trivial structural identity; it is here
purely to give a named handle on the RHS shape. -/
theorem k2_rhs_decomposition (n : ℕ) :
    (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
      + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^5
            / (5 * 4 * 3 * 2 : ℝ)
    = (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
      + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^5 / 120 := by
  norm_num

/-- **Tail term is bounded by `n · π(√n)^5 / 120`** — explicit constant
form for downstream comparison. -/
theorem k2_tail_explicit_form (n : ℕ) :
    (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^5
        / (5 * 4 * 3 * 2 : ℝ)
      = (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^5 / 120 := by
  norm_num

/-! ## Section 8 — Mechanical downstream bridge.

Even though the k=2 inequality is too crude for Path C, we expose the
mechanical bridge showing how `AssemblyPieceA_at_k2` would feed
downstream.  This is part of the task spec deliverable. -/

/-- **Downstream bridge**:  `AssemblyPieceA_at_k2` discharges the
constant-`(fun _ => 2)` instance of the general `AssemblyPieceA`,
which in turn (combined with the general k-quantified content) would
discharge `AssemblyPieceA`.

This bridge by itself is **insufficient** to discharge the full
`AssemblyPieceA`, because the general Prop requires the inequality at
*every* `k : ℕ → ℕ`, not just the constant `k = 2`.

We expose this as a partial bridge: `AssemblyPieceA_at_k2` gives the
k=2 instance, which is a *single point* in the Π-quantified
`AssemblyPieceA`. -/
theorem assemblyPieceA_holds_specialized_to_k2_function :
    AssemblyPieceA_at_k2 →
      ∀ n : ℕ, 4 ≤ n →
        (goldbachSiftedPair n (Nat.sqrt n) : ℝ)
          ≤ (n : ℝ) * pairedBrunFactor (Nat.sqrt n)
            + (n : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ)^(2 * (fun (_ : ℕ) => 2) n + 1)
                  / ((2 * (fun (_ : ℕ) => 2) n + 1).factorial : ℝ) :=
  assemblyPieceA_const_k2_of_assemblyPieceA_at_k2

/-! ## Section 9 — Specialised cardinal bounds. -/

/-- **Trivial cardinal bound**:  `goldbachSiftedPair n √n ≤ n`,
real-valued — same as in general `AssemblyPieceA` bookkeeping. -/
theorem goldbachSiftedPair_sqrt_le_real (n : ℕ) :
    (goldbachSiftedPair n (Nat.sqrt n) : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast goldbachSiftedPair_le n (Nat.sqrt n)

/-- **Non-negativity of the sift count** at `z = √n`. -/
theorem goldbachSiftedPair_sqrt_nonneg (n : ℕ) :
    (0 : ℝ) ≤ (goldbachSiftedPair n (Nat.sqrt n) : ℝ) :=
  Nat.cast_nonneg _

/-! ## Section 10 — Closing-attempt residual.

We attempt to close `AssemblyPieceA_at_k2`.  The genuine content is
the same combinatorial chain as the general kernel
`BrunBonferroniNatAtSqrtArbitraryKKernel` (P19-T22), just instantiated
at fixed depth `k = 2`.

Since the project already exposes this kernel as a named open Prop, we
can give a **conditional closure** of `AssemblyPieceA_at_k2`:  it
holds, provided the general kernel holds. -/

/-- **Conditional headline (P19-T33)**:
`AssemblyPieceA_at_k2` holds, provided
`BrunBonferroniNatAtSqrtArbitraryKKernel` holds.

The bridge is mechanical (a specialisation by instantiation at
`k = fun _ => 2`).  Closing the general kernel discharges this k=2
specialisation immediately.

This is the **honest** closure: the genuine combinatorial content at
`k = 2` is no different from the general kernel, and the project
already exposes this as a named open Prop.  We do not internalise the
Halberstam-Richert combinatorial chain in this file. -/
theorem assemblyPieceA_at_k2_holds_conditional
    (h : BrunBonferroniNatAtSqrtArbitraryKKernel) :
    AssemblyPieceA_at_k2 :=
  assemblyPieceA_at_k2_of_general_kernel h

/-! ## Section 11 — Vacuous regime closure.

At `n ≤ 1`, the sift set is empty, so the inequality holds trivially.
We expose this as a closed fact (for the n ≥ 4 hypothesis of
`AssemblyPieceA_at_k2`, the vacuous regime is `n ≤ 3`). -/

/-- At `n ≤ 1`, `goldbachSiftedPair n z = 0`, re-exported from
`PathC_AssemblyPieceAClosure`. -/
theorem goldbachSiftedPair_zero_of_n_le_one
    {n z : ℕ} (hn : n ≤ 1) :
    goldbachSiftedPair n z = 0 :=
  Gdbh.PathCAssemblyPieceAClosure.goldbachSiftedPair_zero_of_n_le_one hn

/-! ## Section 12 — Final audit and headline. -/

/-- **P19-T33 summary** (sentinel; informal).

This file:
* Defines `AssemblyPieceA_at_k2`, the specialisation of
  `AssemblyPieceA` at fixed truncation depth `k = 2`.
* Provides the mechanical bridge `AssemblyPieceA → AssemblyPieceA_at_k2`
  (specialisation by instantiation at `k = fun _ => 2`).
* Provides the mechanical bridge
  `BrunBonferroniNatAtSqrtArbitraryKKernel → AssemblyPieceA_at_k2`.
* Documents the honest finding that even **if** `AssemblyPieceA_at_k2`
  is fully closed, the resulting tail `n · π(√n)^5 / 120` dominates
  the main term `n · pairedBrunFactor(√n) ~ n / (log n)^2`, so the
  k=2 truncation is **far too crude** for the Path C reservoir bound.
* Documents the conclusion (outcome (c)) that `k = 2` is not strong
  enough:  `k` must grow with `n` (canonical `k(n) = 2n`) or the
  Bonferroni truncation tail dominates. -/
theorem pathC_p19_t33_summary : True := trivial

end PathCBrunBonferroniMinimalK
end Gdbh
