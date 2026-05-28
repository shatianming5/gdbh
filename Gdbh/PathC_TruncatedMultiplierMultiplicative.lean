/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P25-T3 (Phase 25 / Path C — Multiplicative structure of
        `truncatedGoldbachSingularMultiplier`).
-/
import Gdbh.PathC_GoldbachLocalFactor
import Gdbh.PathC_HardyLittlewoodForm

/-!
# Path C — P25-T3: Multiplicative structure of `truncatedGoldbachSingularMultiplier`

This file proves multiplicativity-type properties of the truncated
Goldbach singular multiplier

```
truncatedGoldbachSingularMultiplier n z =
  ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
    if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1
```

(see `Gdbh.PathCGoldbachLocalFactor`).  The key observation is that
the *only* dependence on `n` is through the predicate `p ∣ n` for
primes `p` in the truncation range; in particular, the multiplier
depends only on the **prime divisor support** of `n`, not on the
exponents.  This makes it a multiplicative arithmetic function in the
classical sense: for coprime `n₁, n₂`,

```
truncatedGoldbachSingularMultiplier (n₁ * n₂) z =
  truncatedGoldbachSingularMultiplier n₁ z *
  truncatedGoldbachSingularMultiplier n₂ z .
```

The mechanism, prime by prime in the truncation range:

* For coprime `n₁, n₂` and a prime `p`, we cannot have both `p ∣ n₁`
  and `p ∣ n₂` (else `p ∣ gcd = 1`).
* By `Nat.Prime.dvd_mul`, `p ∣ n₁ * n₂` iff `p ∣ n₁ ∨ p ∣ n₂`.
* The local factor at `p` (in the truncated multiplier) is `1` unless
  `p ∣ n`, in which case it is `1 + 1/(p-2)`.

Hence the local factor for `n₁ * n₂` equals the product of those for
`n₁` and `n₂` pointwise at every prime; multiplying over primes in
the truncation range gives the global multiplicativity.

We also record:

* `truncatedGoldbachSingularMultiplier_one`:  the multiplier at `n = 1`
  equals `1`.
* `truncatedGoldbachSingularMultiplier_depends_on_support`:  the
  multiplier depends only on the divisibility predicate `p ∣ n` for
  primes in the range, i.e. is invariant under any change of `n`
  that preserves prime support inside `[3, z]`.
* Bridge to the singular series for *primorial-like* inputs (any `n`
  divisible by every prime in `[3, z]`):  the multiplier collapses to
  the obvious explicit product `∏ (1 + 1/(p-2))`.
* CRT connection:  multiplicativity implies that for any squarefree
  factorization of `n` into pairwise coprime parts, the multiplier
  factorizes accordingly — this is the abstract CRT shape of the local
  density.

The file is `sorry`/`axiom`/`admit`-free.
-/

namespace Gdbh
namespace PathCTruncatedMultiplierMultiplicative

open scoped BigOperators
open Gdbh.PathCGoldbachLocalFactor (truncatedGoldbachSingularMultiplier
  truncatedGoldbachSingularMultiplier_ge_one goldbachSingularMultiplier)
open Gdbh.PathCHardyLittlewoodForm (singularSeries)

/-! ## Section 1 — Pointwise factor analysis -/

/-- Abbreviation for the local factor at a prime `p` in the truncated
multiplier:  `1 + 1/(p-2)` if `p ∣ n`, else `1`. -/
private noncomputable def localFactor (n p : ℕ) : ℝ :=
  if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1

/-- The truncated multiplier as a product of `localFactor`. -/
private lemma truncated_eq_localFactor_prod (n z : ℕ) :
    truncatedGoldbachSingularMultiplier n z
      = ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime, localFactor n p := by
  classical
  unfold truncatedGoldbachSingularMultiplier
  rfl

/-- The local factor at a prime `p ≥ 3` is positive. -/
private lemma localFactor_pos {p : ℕ} (hp : 3 ≤ p) (n : ℕ) :
    (0 : ℝ) < localFactor n p := by
  unfold localFactor
  by_cases h : p ∣ n
  · simp only [if_pos h]
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hpos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have : (0 : ℝ) < 1 + 1 / ((p : ℝ) - 2) := by
      have h1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 2) := le_of_lt (one_div_pos.mpr hpos)
      linarith
    exact this
  · simp only [if_neg h]; exact one_pos

/-- The local factor at a prime `p ≥ 3` is at least `1`. -/
private lemma one_le_localFactor {p : ℕ} (hp : 3 ≤ p) (n : ℕ) :
    (1 : ℝ) ≤ localFactor n p := by
  unfold localFactor
  by_cases h : p ∣ n
  · simp only [if_pos h]
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hpos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have h1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 2) := le_of_lt (one_div_pos.mpr hpos)
    linarith
  · simp only [if_neg h]; exact le_refl 1

/-- **Pointwise multiplicativity of the local factor.**  For coprime
`n₁, n₂` and any prime `p`,

```
localFactor (n₁ * n₂) p = localFactor n₁ p · localFactor n₂ p .
```

This is the engine of the global multiplicativity result below. -/
private lemma localFactor_mul_of_coprime {n₁ n₂ p : ℕ}
    (hp : Nat.Prime p) (hcop : Nat.Coprime n₁ n₂) :
    localFactor (n₁ * n₂) p = localFactor n₁ p * localFactor n₂ p := by
  unfold localFactor
  -- We case-split on whether `p ∣ n₁`, `p ∣ n₂`, and `p ∣ n₁*n₂`.
  -- By `Nat.Prime.dvd_mul`, the last is equivalent to the disjunction
  -- of the first two; by coprimality, the first two cannot both hold.
  by_cases h1 : p ∣ n₁
  · -- `p ∣ n₁`.  Then `p ∤ n₂` (else `p ∣ gcd(n₁,n₂) = 1`, contradiction).
    have h2 : ¬ p ∣ n₂ := by
      intro h2
      have hdvd : p ∣ Nat.gcd n₁ n₂ := Nat.dvd_gcd h1 h2
      have h_eq : Nat.gcd n₁ n₂ = 1 := hcop
      rw [h_eq] at hdvd
      have hp_gt : 1 < p := hp.one_lt
      have hp_le : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    -- `p ∣ n₁ * n₂` since `p ∣ n₁`.
    have h12 : p ∣ n₁ * n₂ := Dvd.dvd.mul_right h1 n₂
    simp [h1, h2, h12]
  · by_cases h2 : p ∣ n₂
    · -- `p ∤ n₁`, `p ∣ n₂`.  Still `p ∣ n₁ * n₂`.
      have h12 : p ∣ n₁ * n₂ := Dvd.dvd.mul_left h2 n₁
      simp [h1, h2, h12]
    · -- Neither, so `p ∤ n₁ * n₂` by primality.
      have h12 : ¬ p ∣ n₁ * n₂ := by
        intro hd
        rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
        · exact h1 h
        · exact h2 h
      simp [h1, h2, h12]

/-! ## Section 2 — Global multiplicativity over the truncation range -/

/-- **Multiplicativity of the truncated Goldbach singular multiplier.**

For coprime `n₁, n₂` and any sieve level `z`,

```
truncatedGoldbachSingularMultiplier (n₁ * n₂) z =
  truncatedGoldbachSingularMultiplier n₁ z *
  truncatedGoldbachSingularMultiplier n₂ z .
```
-/
theorem truncatedGoldbachSingularMultiplier_mul_of_coprime
    (n₁ n₂ z : ℕ) (hcop : Nat.Coprime n₁ n₂) :
    truncatedGoldbachSingularMultiplier (n₁ * n₂) z
      = truncatedGoldbachSingularMultiplier n₁ z
        * truncatedGoldbachSingularMultiplier n₂ z := by
  classical
  rw [truncated_eq_localFactor_prod (n := n₁ * n₂),
      truncated_eq_localFactor_prod (n := n₁),
      truncated_eq_localFactor_prod (n := n₂)]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨_hpIcc, hpp⟩
  exact localFactor_mul_of_coprime hpp hcop

/-! ## Section 3 — Edge values and support-only dependence -/

/-- At `n = 1`, the truncated multiplier is `1`:  no prime divides `1`,
so every local factor is `1`. -/
@[simp] theorem truncatedGoldbachSingularMultiplier_one (z : ℕ) :
    truncatedGoldbachSingularMultiplier 1 z = 1 := by
  classical
  unfold truncatedGoldbachSingularMultiplier
  refine Finset.prod_eq_one ?_
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpp⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
  -- `p ≥ 3` and `p` prime, so `p ∤ 1`.
  have hnotdvd : ¬ p ∣ 1 := by
    intro hd
    have hple1 : p ≤ 1 := Nat.le_of_dvd (by norm_num) hd
    omega
  simp [hnotdvd]

/-- Multiplying by `1` does not change the multiplier (formal sanity
check; follows from `truncatedGoldbachSingularMultiplier_one` together
with the multiplicativity theorem and the trivial coprimality
`Nat.Coprime n 1`). -/
theorem truncatedGoldbachSingularMultiplier_mul_one (n z : ℕ) :
    truncatedGoldbachSingularMultiplier (n * 1) z
      = truncatedGoldbachSingularMultiplier n z := by
  have hcop : Nat.Coprime n 1 := Nat.coprime_one_right n
  rw [truncatedGoldbachSingularMultiplier_mul_of_coprime n 1 z hcop,
      truncatedGoldbachSingularMultiplier_one]
  ring

/-- **Support-only dependence.**  If two natural numbers `n` and `m`
have the same divisor pattern at every prime in `[3, z]`, then their
truncated multipliers agree.  This is the precise sense in which the
multiplier depends only on the prime support inside the truncation
range. -/
theorem truncatedGoldbachSingularMultiplier_congr_of_support
    {n m z : ℕ}
    (h : ∀ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (p ∣ n ↔ p ∣ m)) :
    truncatedGoldbachSingularMultiplier n z
      = truncatedGoldbachSingularMultiplier m z := by
  classical
  unfold truncatedGoldbachSingularMultiplier
  refine Finset.prod_congr rfl ?_
  intro p hp
  by_cases hpn : p ∣ n
  · have hpm : p ∣ m := (h p hp).mp hpn
    simp [hpn, hpm]
  · have hpm : ¬ p ∣ m := fun hd => hpn ((h p hp).mpr hd)
    simp [hpn, hpm]

/-! ## Section 4 — General iterated multiplicativity over coprime
finite tuples (CRT shape) -/

/-- **Iterated multiplicativity over a pairwise-coprime indexed family.**

For a finite indexed family `(f : ι → ℕ)` whose values are pairwise
coprime (over a finset `s`),

```
truncatedGoldbachSingularMultiplier (∏ i ∈ s, f i) z =
  ∏ i ∈ s, truncatedGoldbachSingularMultiplier (f i) z .
```

This is the abstract CRT shape of the local-density formula:  any
CRT-style decomposition `n = ∏ nᵢ` with pairwise-coprime `nᵢ` (e.g. a
canonical squarefree factorisation into prime powers) factorises the
multiplier accordingly. -/
theorem truncatedGoldbachSingularMultiplier_prod_of_pairwise_coprime
    {ι : Type*} (s : Finset ι) (f : ι → ℕ) (z : ℕ)
    (h : (s : Set ι).Pairwise (fun i j => Nat.Coprime (f i) (f j))) :
    truncatedGoldbachSingularMultiplier (∏ i ∈ s, f i) z
      = ∏ i ∈ s, truncatedGoldbachSingularMultiplier (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi IH =>
      -- `∏ i ∈ insert i s, f i = f i * ∏ j ∈ s, f j`, and `f i` is
      -- coprime to every `f j` for `j ∈ s`, hence to their product.
      have h_sub : (s : Set ι).Pairwise (fun i j => Nat.Coprime (f i) (f j)) := by
        intro a ha b hb hab
        refine h ?_ ?_ hab
        · exact Finset.mem_insert.mpr (Or.inr ha)
        · exact Finset.mem_insert.mpr (Or.inr hb)
      have hIH := IH h_sub
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      -- We need:  `f i` coprime to `∏ j ∈ s, f j`.
      have h_cop_prod : Nat.Coprime (f i) (∏ j ∈ s, f j) := by
        refine Nat.Coprime.prod_right ?_
        intro j hj
        have hi_ne_j : i ≠ j := fun heq => hi (heq ▸ hj)
        exact h (Finset.mem_insert_self i s)
          (Finset.mem_insert.mpr (Or.inr hj)) hi_ne_j
      rw [truncatedGoldbachSingularMultiplier_mul_of_coprime _ _ _ h_cop_prod,
          hIH]

/-! ## Section 5 — Bridge to the singular series for primorial-style
inputs -/

/-- **Primorial-style explicit form.**  If every odd prime in `[3, z]`
divides `n`, then the truncated multiplier collapses to the explicit
product

```
truncatedGoldbachSingularMultiplier n z =
  ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 + 1 / ((p : ℝ) - 2)) .
```

This is the "primorial" regime where every local factor is genuinely
present;  it is the upper envelope of the multiplier over all `n` at a
given truncation level. -/
theorem truncatedGoldbachSingularMultiplier_of_all_primes_dvd
    {n z : ℕ}
    (h : ∀ p ∈ (Finset.Icc 3 z).filter Nat.Prime, p ∣ n) :
    truncatedGoldbachSingularMultiplier n z
      = ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
          (1 + 1 / ((p : ℝ) - 2)) := by
  classical
  unfold truncatedGoldbachSingularMultiplier
  refine Finset.prod_congr rfl ?_
  intro p hp
  simp [h p hp]

/-- **Symmetric upper envelope.**  Among all `n`, the truncated multiplier
at sieve level `z` is uniformly bounded above by the primorial-style
explicit form:

```
truncatedGoldbachSingularMultiplier n z ≤
  ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime, (1 + 1 / ((p : ℝ) - 2)) .
```
-/
theorem truncatedGoldbachSingularMultiplier_le_primorial_envelope
    (n z : ℕ) :
    truncatedGoldbachSingularMultiplier n z
      ≤ ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
          (1 + 1 / ((p : ℝ) - 2)) := by
  classical
  unfold truncatedGoldbachSingularMultiplier
  refine Finset.prod_le_prod ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, _⟩
    rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hpos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have h1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 2) := le_of_lt (one_div_pos.mpr hpos)
    by_cases hpn : p ∣ n
    · rw [if_pos hpn]; linarith
    · rw [if_neg hpn]; exact zero_le_one
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, _⟩
    rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hpos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have h1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 2) := le_of_lt (one_div_pos.mpr hpos)
    by_cases hpn : p ∣ n
    · rw [if_pos hpn]
    · rw [if_neg hpn]; linarith

/-! ## Section 6 — CRT-locality connection at the singular-series level -/

/-- **Truncated multiplier vs. singular series at sieve level `z = n`.**

By definition `goldbachSingularMultiplier n = truncatedGoldbachSingularMultiplier n n`.
The local factor `1 + 1/(p-2)` agrees with the singular-series factor
`(p-1)/(p-2)`, so the truncated multiplier and the singular series have
the same "shape":  both are products of `(p-1)/(p-2)` over primes in
`[3, z]` (resp. `[3, n]`) dividing `n`.  At `z = n` they agree on the
divisor set.

Here we record the per-factor algebraic identity in clean form,
without going through the `truncated_eq_div_prod` path in
`PathC_BrunGoldbachSingularClosure.lean`.  -/
theorem localFactor_eq_singular_factor {p : ℕ} (hp : 3 ≤ p) (n : ℕ) :
    (if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1)
      = if p ∣ n then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by
  by_cases hpn : p ∣ n
  · simp only [if_pos hpn]
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hpos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    field_simp
    ring
  · simp [hpn]

/-! ## Section 7 — Compatibility with the full `goldbachSingularMultiplier` -/

/-- `goldbachSingularMultiplier` (defined as
`truncatedGoldbachSingularMultiplier n n`) is multiplicative on coprime
pairs, *but the truncation parameter must match the product `n₁ * n₂`*.
The honest statement is therefore that the *truncated* multipliers
at the common sieve level `z = n₁ * n₂` factorise; in particular,

```
goldbachSingularMultiplier (n₁ * n₂)
  = truncatedGoldbachSingularMultiplier n₁ (n₁ * n₂)
    * truncatedGoldbachSingularMultiplier n₂ (n₁ * n₂) .
```
-/
theorem goldbachSingularMultiplier_mul_of_coprime
    {n₁ n₂ : ℕ} (hcop : Nat.Coprime n₁ n₂) :
    goldbachSingularMultiplier (n₁ * n₂)
      = truncatedGoldbachSingularMultiplier n₁ (n₁ * n₂)
        * truncatedGoldbachSingularMultiplier n₂ (n₁ * n₂) := by
  unfold goldbachSingularMultiplier
  exact truncatedGoldbachSingularMultiplier_mul_of_coprime n₁ n₂ (n₁ * n₂) hcop

/-! ## Section 8 — Diagnostics and axiom audit hook -/

/-- A diagnostic packaging theorem assembling the main outputs of this
file:  multiplicativity, support-only dependence, the primorial-style
explicit form, and the upper envelope. -/
theorem truncatedMultiplier_multiplicative_package
    (n₁ n₂ z : ℕ) (hcop : Nat.Coprime n₁ n₂) :
    truncatedGoldbachSingularMultiplier (n₁ * n₂) z
        = truncatedGoldbachSingularMultiplier n₁ z
          * truncatedGoldbachSingularMultiplier n₂ z
      ∧ truncatedGoldbachSingularMultiplier n₁ z
          ≤ ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime,
              (1 + 1 / ((p : ℝ) - 2)) := by
  refine ⟨?_, ?_⟩
  · exact truncatedGoldbachSingularMultiplier_mul_of_coprime n₁ n₂ z hcop
  · exact truncatedGoldbachSingularMultiplier_le_primorial_envelope n₁ z

end PathCTruncatedMultiplierMultiplicative
end Gdbh
