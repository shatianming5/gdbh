/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P12-T1 (Phase 12 / deepest mathlib-gap closure — Mertens 1st)
-/
import Gdbh.PathC_MertensSecondProof
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Path C — Mertens' First Theorem decomposition (P12-T1)

This file is the **P12-T1 deliverable** in Phase 12 (deepest
mathlib-gap closure).  Its target is the named open Prop
`Gdbh.PathCMertensSecondProof.MertensFirstTheoremBound`:

```
∃ B : ℝ, ∃ z₀ : ℕ, ∀ z ≥ z₀,
  |Σ_{p ≤ z, p prime} log p / p  −  log z|  ≤  B .
```

(P12-T1 target — Mertens 1874 first theorem.  Mathlib v4.29.1:
**no Mertens-style file**.  This is the deepest analytic atom of
Path C.)

## Strategy — classical von Mangoldt decomposition

Mertens' first theorem is classically derived from the von
Mangoldt-Chebyshev identity

```
Σ_{n ≤ N} Λ(n) / n  =  log N + O(1) ,
```

where `Λ` is the von Mangoldt function.  One then **splits Λ** along
the prime / prime-power decomposition:

```
Λ(n) / n  =  [n is prime] · log p / p
              +  [n = p^k, k ≥ 2] · log p / p^k .
```

Summing over `n ≤ N`:

```
Σ_{n ≤ N} Λ(n)/n  =  Σ_{p ≤ N, prime} log p / p  +  Σ_{p^k ≤ N, k ≥ 2} log p / p^k .
```

The **tail** (`k ≥ 2`) sum is uniformly bounded in `N` because

```
Σ_{p prime} Σ_{k ≥ 2} log p / p^k  =  Σ_p log p / (p (p-1))  ≤  Σ_n log n / (n²)  <  ∞ .
```

Combining: `Σ log p / p = (log N + O(1)) − O(1) = log N + O(1)`.  ✓

## Sub-Props introduced

* `VonMangoldtSumLogN` — `∃ C, ∀ N ≥ N₀, |Σ_{n ≤ N} Λ(n)/n − log N| ≤ C`.
  *Open* mathlib-gap (the von Mangoldt asymptotic identity; itself
  classical, ~2 weeks of formalization).

* `PrimePowerTailBound` — `∃ B', ∀ N, Σ_{n ≤ N, IsPrimePow n, ¬ n.Prime}
  Λ(n)/n ≤ B'`.  The bounded tail of higher prime powers (`k ≥ 2`).
  *Closeable in principle* from `Summable.tsum_one_div_nat_pow` (`Σ
  1/n^2 < ∞`) and Λ-bounds (`Λ(p^k) ≤ log(p^k) = k log p ≤ p^k`);
  here left as a named gap with a precise statement.

* `VonMangoldtSplitIdentity` — *identity* (not a bound):
  `∀ N, Σ_{n ≤ N} Λ(n)/n =
    (Σ_{p prime, p ≤ N} log p / p) + (Σ_{n ≤ N, IsPrimePow n, ¬n.Prime} Λ(n)/n)`.
  Pure rearrangement; closeable axiom-cleanly.

## What's closed vs. open in this file

**Closed axiom-clean (only `Classical.choice, Quot.sound, propext`)**:

* `vonMangoldtSplitIdentity` — the partition identity.
* `mertensFirstTheoremBound_of_components` — the mechanical assembly
  bridge: `VonMangoldtSumLogN × PrimePowerTailBound → MertensFirstTheoremBound`.
* `mertensSecondLowerBoundOdd_of_first_components` — composed
  end-to-end with P11-T1: `VonMangoldtSumLogN × PrimePowerTailBound ×
  AbelInversionMertensSecondFromFirst → MertensSecondLowerBoundOdd`.

**Open (named gaps, *strictly weaker* than `MertensFirstTheoremBound`)**:

* `VonMangoldtSumLogN` — the genuine analytic input.
* `PrimePowerTailBound` — convergent tail series bound (closeable via
  p-series comparison; left as named gap for future explicit-constant
  extraction work).

## Axiom budget

All theorems below are axiom-clean: only
`Classical.choice, Quot.sound, propext`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine
  angew. Math. 78 (1874), 46–62, Theorem 1.
* G. H. Hardy, E. M. Wright, *Theory of Numbers*, §22.7.
* T. Tao, *Analytic Prime Number Theory*, Theorem 1.10.
-/

namespace Gdbh
namespace PathCMertensFirstProof

open Real Finset
open Gdbh.PathCMertensSecondProof
open ArithmeticFunction

/-! ## Section 1 — Named open sub-Props -/

/-- **Named open Prop**: the *von Mangoldt asymptotic identity*.

```
∃ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
  |Σ_{1 ≤ n ≤ N} Λ(n) / n  −  log N|  ≤  C .
```

The classical Chebyshev-Mertens identity for the von Mangoldt sum.
Mathlib v4.29.1 status: **open** (no `Λ/n`-asymptotic theorem).
Classically derived from `Σ_{n ≤ N} Λ(n) = ψ(N)` and Abel summation
against `1/n`, using `ψ(N) = N + O(N / log N)` (the prime-number
theorem in its weakest form) — but a much weaker `ψ(N) = O(N)`
already suffices to *get the upper bound* via partial summation. -/
def VonMangoldtSumLogN : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∑ n ∈ Finset.Icc 1 N, (Λ n / (n : ℝ))) - Real.log (N : ℝ)| ≤ C

/-- **Named open Prop**: uniform bound on the *prime-power tail*.

```
∃ B' : ℝ, ∀ N : ℕ,
  Σ_{n ≤ N, IsPrimePow n, ¬n.Prime} Λ(n) / n  ≤  B' .
```

The non-prime prime-power tail sum `Σ_{p^k, k ≥ 2} log p / p^k`.  This
is a convergent series:

```
Σ_p Σ_{k ≥ 2} log p / p^k  =  Σ_p (log p) / (p(p-1))  ≤  Σ_p (log p) / (p²/2)
  ≤  2 · Σ_n (log n) / n²  <  ∞ .
```

The total mass is `≤ 1` numerically (`Σ_{p, k≥2} log p / p^k ≈ 0.755`).
Closeable from mathlib's `summable_one_div_nat_pow` (p-series with
`p = 2`) plus `Λ`-pointwise upper bounds; left here as a named gap. -/
def PrimePowerTailBound : Prop :=
  ∃ B' : ℝ, ∀ N : ℕ,
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        (Λ n / (n : ℝ))) ≤ B'

/-! ## Section 2 — The split identity (mechanical) -/

/-- **Mechanical identity**: the von Mangoldt sum partitions into a
prime contribution plus a non-prime prime-power tail.

```
Σ_{1 ≤ n ≤ N} Λ(n) / n
  =  (Σ_{p prime, 2 ≤ p ≤ N} log p / p)
       +  (Σ_{n ≤ N, IsPrimePow n, ¬n.Prime} Λ(n) / n) .
```

Pure rearrangement: split the Λ-support set `{n ≤ N : IsPrimePow n}`
along the disjoint partition `{Prime} ⊔ {¬Prime}`, use
`Λ(p) = log p` for primes, and absorb the `Λ ≡ 0` complement.

(Closed axiom-clean.) -/
theorem vonMangoldtSplitIdentity (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Λ n / (n : ℝ)))
      = (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
          Real.log (p : ℝ) / (p : ℝ))
        + (∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
            (Λ n / (n : ℝ))) := by
  -- Step 1: zero out terms where Λ vanishes (i.e. ¬ IsPrimePow).
  have hzero : ∀ n ∈ Finset.Icc 1 N, ¬ IsPrimePow n → Λ n / (n : ℝ) = 0 := by
    intro n _ hnpp
    have : Λ n = 0 := vonMangoldt_eq_zero_iff.mpr hnpp
    simp [this]
  -- Step 2: split the sum over `Icc 1 N` along the IsPrimePow predicate.
  have hsplit_isPP :
      (∑ n ∈ Finset.Icc 1 N, (Λ n / (n : ℝ)))
        = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n),
            (Λ n / (n : ℝ)) := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro n hn hne
    by_contra hnotPP
    exact hne (by
      have : Λ n = 0 := vonMangoldt_eq_zero_iff.mpr hnotPP
      simp [this])
  -- Step 3: within the IsPrimePow filter, split along Prime / ¬Prime.
  have hsplit_prime :
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n),
          (Λ n / (n : ℝ))
        = (∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => IsPrimePow n ∧ n.Prime), (Λ n / (n : ℝ)))
          + (∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => IsPrimePow n ∧ ¬ n.Prime), (Λ n / (n : ℝ))) := by
    classical
    -- partition the IsPrimePow filter into Prime / ¬Prime.
    rw [← Finset.sum_filter_add_sum_filter_not
        ((Finset.Icc 1 N).filter (fun n => IsPrimePow n))
        (fun n => n.Prime) (fun n => Λ n / (n : ℝ))]
    congr 1
    · apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext n
      simp [Finset.mem_filter, and_assoc, and_comm, and_left_comm]
    · apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext n
      simp [Finset.mem_filter, and_assoc, and_comm, and_left_comm]
  -- Step 4: identify the Prime-piece with the target prime sum.
  have hprime_piece :
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.Prime),
          (Λ n / (n : ℝ))
        = ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
            Real.log (p : ℝ) / (p : ℝ) := by
    -- The two index sets are equal as Finsets, and Λ p = log p on primes.
    have hset_eq :
        (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.Prime)
          = (Finset.Icc 2 N).filter Nat.Prime := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨_, hle⟩, _, hp⟩
        refine ⟨⟨?_, hle⟩, hp⟩
        exact hp.two_le
      · rintro ⟨⟨h1, h2⟩, hp⟩
        refine ⟨⟨?_, h2⟩, hp.isPrimePow, hp⟩
        omega
    rw [hset_eq]
    apply Finset.sum_congr rfl
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨_, hp⟩
    -- Λ p = log p for primes.
    have hΛp : Λ n = Real.log (n : ℝ) := vonMangoldt_apply_prime hp
    rw [hΛp]
  -- Combine.
  rw [hsplit_isPP, hsplit_prime, hprime_piece]

/-! ## Section 3 — Mechanical assembly bridge -/

/-- **Mechanical assembly**: `MertensFirstTheoremBound` follows from
the two sub-Props by the von Mangoldt split identity and the triangle
inequality.

Reasoning chain (with `S_p := Σ_{p ≤ N} log p / p` and
`S_t := Σ_{prime powers k ≥ 2, ≤ N} Λ/id`):

1. `Σ Λ(n)/n = S_p + S_t` (split identity).
2. `|Σ Λ(n)/n − log N| ≤ C` (input `VonMangoldtSumLogN`).
3. `0 ≤ S_t ≤ B'` (input `PrimePowerTailBound` — `Λ` is nonneg).
4. Triangle: `|S_p − log N| = |Σ Λ/n − S_t − log N|
                            ≤ |Σ Λ/n − log N| + |S_t| ≤ C + B'`.

Set `B = C + B'`, `z₀ = max N₀ 1`.  (Closed axiom-clean.) -/
theorem mertensFirstTheoremBound_of_components
    (hVM : VonMangoldtSumLogN)
    (hTail : PrimePowerTailBound) :
    MertensFirstTheoremBound := by
  obtain ⟨C, N₀, hVMbound⟩ := hVM
  obtain ⟨B', hTbound⟩ := hTail
  refine ⟨C + B', N₀, ?_⟩
  intro N hN
  -- Use the split identity.
  have hsplit := vonMangoldtSplitIdentity N
  -- Abbreviate.
  set Sall := (∑ n ∈ Finset.Icc 1 N, (Λ n / (n : ℝ))) with hSall_def
  set Sp := (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
              Real.log (p : ℝ) / (p : ℝ)) with hSp_def
  set St := (∑ n ∈ (Finset.Icc 1 N).filter
                (fun n => IsPrimePow n ∧ ¬ n.Prime),
              (Λ n / (n : ℝ))) with hSt_def
  -- hsplit : Sall = Sp + St
  -- hVMbound : |Sall − log N| ≤ C
  -- hTbound : St ≤ B'
  -- St is nonneg since each term is.
  have hSt_nonneg : 0 ≤ St := by
    refine Finset.sum_nonneg ?_
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hmem, _⟩
    rcases Finset.mem_Icc.mp hmem with ⟨hn1, _⟩
    apply div_nonneg vonMangoldt_nonneg
    exact_mod_cast Nat.zero_le n
  have hSt_le := hTbound N  -- St ≤ B'
  have hbound : |Sall - Real.log (N : ℝ)| ≤ C := hVMbound N hN
  -- |Sp − log N| = |Sall − St − log N| ≤ |Sall − log N| + |St|
  have heq : Sp = Sall - St := by
    -- From hsplit : Sall = Sp + St
    linarith [hsplit]
  have habs_St : |St| = St := abs_of_nonneg hSt_nonneg
  have habs_St_le : |St| ≤ B' := by
    rw [habs_St]; exact hSt_le
  -- B' may be negative if the bound is vacuous; but since 0 ≤ St ≤ B', B' ≥ 0.
  have hB'_nonneg : 0 ≤ B' := le_trans hSt_nonneg hSt_le
  calc |Sp - Real.log (N : ℝ)|
      = |Sall - St - Real.log (N : ℝ)| := by rw [heq]
    _ = |(Sall - Real.log (N : ℝ)) - St| := by ring_nf
    _ ≤ |Sall - Real.log (N : ℝ)| + |St| := abs_sub _ _
    _ ≤ C + B' := add_le_add hbound habs_St_le

/-! ## Section 4 — End-to-end composition with P11-T1 -/

/-- **Composed reduction (P12-T1 + P11-T1)**: the named open
`MertensSecondLowerBoundOdd` follows from the three smaller named
open Props introduced across P11-T1 and P12-T1:

```
VonMangoldtSumLogN  +  PrimePowerTailBound  +  AbelInversionMertensSecondFromFirst
  ⇒  MertensSecondLowerBoundOdd .
```

Chain:
1. `VonMangoldtSumLogN` + `PrimePowerTailBound` ⇒
   `MertensFirstTheoremBound`  (this file, P12-T1).
2. `MertensFirstTheoremBound` + `AbelInversionMertensSecondFromFirst` ⇒
   `MertensSecondLowerBoundOdd`  (P11-T1).

(Closed axiom-clean.) -/
theorem mertensSecondLowerBoundOdd_of_first_components
    (hVM : VonMangoldtSumLogN)
    (hTail : PrimePowerTailBound)
    (hAbel : AbelInversionMertensSecondFromFirst) :
    Gdbh.PathCMertensThirdProof.MertensSecondLowerBoundOdd :=
  Gdbh.PathCMertensSecondProof.mertensSecondLowerBoundOdd_of_components
    (mertensFirstTheoremBound_of_components hVM hTail)
    hAbel

/-! ## Section 5 — Summary -/

/-- **P12-T1 summary, in proof form.**

This file decomposes the named open `MertensFirstTheoremBound` (the
deepest analytic atom of Path C) into two strictly smaller named open
sub-Props:

1. `VonMangoldtSumLogN` — the von Mangoldt asymptotic
   `Σ_{n ≤ N} Λ(n)/n = log N + O(1)`.

2. `PrimePowerTailBound` — uniform bound on the non-prime prime-power
   tail `Σ_{p^k ≤ N, k ≥ 2} log p / p^k` (a convergent series).

Of the **mechanical** bridges, the following are closed
axiom-cleanly in this file:

* `vonMangoldtSplitIdentity` — the partition identity
  `Σ Λ/id = Σ_p log p / p + Σ_{prime powers k≥2} Λ/id`.

* `mertensFirstTheoremBound_of_components` — the headline assembly
  `VonMangoldtSumLogN × PrimePowerTailBound → MertensFirstTheoremBound`
  (via triangle inequality on the split identity).

* `mertensSecondLowerBoundOdd_of_first_components` — full P11-T1 +
  P12-T1 chain: the three smallest sub-Props imply
  `MertensSecondLowerBoundOdd`.

What remains open after P12-T1: the two sub-Props above.  The
**tail** is a convergent-series bound, closeable in principle from
`summable_one_div_nat_pow` (mathlib v4.29.1) + `Λ`-pointwise
estimates.  The **von Mangoldt asymptotic** is the genuine deep input
(classically Chebyshev's identity for ψ + partial summation; mathlib
status: open).

(Closed axiom-clean.) -/
theorem pathC_p12_t1_summary : True := trivial

end PathCMertensFirstProof
end Gdbh
