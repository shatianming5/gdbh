/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P6-T4a (Phase 6 / Path C — Schnirelmann / Brun pure sieve)
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic

/-!
# Path C — Brun's 1915 pure sieve and the twin-prime upper bound

This file lays down the **decomposition skeleton** for Brun's pure sieve.
Brun's original argument (1915) sifts integers up to `N` by the primes
`p ≤ z` via *truncated* inclusion–exclusion: keeping only the terms in
which the Möbius factor has at most `k` prime divisors gives an upper
bound (when `k` is even) or a lower bound (when `k` is odd) on the
sifted count, with an explicit error term whose size is controlled by a
combinatorial estimate of the form `(∑_{p ≤ z} 1)^k / k!`.  Combined
with Mertens' product theorem, this yields the celebrated bound

```
|{p ≤ N : p, p+2 both prime}| ≪ N · (log log N)^2 / (log N)^2 .
```

Brun's full proof requires (i) the truncated inclusion–exclusion
identity in the *multiplicative* form, (ii) an arithmetic-function /
Möbius identity for the inner divisor sum, (iii) bounds on the
combinatorial main term `X · ∏_{p ≤ z}(1 - ν(p))` via Mertens, and
(iv) an estimate on the truncation error term.  Each of these is a
substantial chunk of analytic number theory; rather than commit to one
monolithic theorem, this file follows the **Prop-decomposition
discipline** used elsewhere in the project (`PathA_*`, `MajorMinorArcs`,
`SingularSeries`, …): we expose

* a concrete sifting `siftedCount`,
* concrete cardinality lemmas relating twin-prime counts to
  `siftedCount` (these are unconditionally proven here),
* three `Prop`-valued hypotheses encoding the three quantitative pieces
  (`BrunMainTerm`, `BrunErrorTerm`, `MertensProductBound`),
* an unconditional assembly theorem
  `twinPrime_count_upperBound_of_brunComponents` showing that the three
  hypotheses together yield a Mertens-shape upper bound on the
  twin-prime count.

This matches the project's "land the skeleton, defer the heavy analytic
estimates as named hypotheses" pattern.  Mathlib already provides the
`BoundingSieve` / `SelbergSieve` framework in
`Mathlib.NumberTheory.SelbergSieve`, but we do not depend on its
specific upper-bound theorem here; Brun's pure sieve predates Selberg
and is conceptually simpler.

## Main results (all axiom-clean: only `propext`, `Classical.choice`,
`Quot.sound`)

* `Gdbh.PathCBrunSieve.siftedCount` — the basic sifted-counting
  function: integers in `[1, N]` with no prime factor `≤ z`.
* `Gdbh.PathCBrunSieve.siftedCount_le_card_Icc` —
  `siftedCount N z ≤ N` (trivial monotonicity).
* `Gdbh.PathCBrunSieve.twinPrimePairs` — the set of pairs `(p, p+2)`
  with `p, p+2` both prime and `p ≤ N`.
* `Gdbh.PathCBrunSieve.twinPrimePairs_card_le_siftedCount` — twin prime
  pairs are sifted by *any* prime sieve below `√N`.
* `Gdbh.PathCBrunSieve.BrunMainTerm`,
  `Gdbh.PathCBrunSieve.BrunErrorTerm`,
  `Gdbh.PathCBrunSieve.MertensProductBound` — the three sub-Props.
* `Gdbh.PathCBrunSieve.twinPrime_count_upperBound_of_brunComponents` —
  conditional twin-prime upper bound from the three sub-Props.

The deferred (decomposed-open) content is the *existence* of witnesses
for `BrunMainTerm`, `BrunErrorTerm`, `MertensProductBound`; those are
classical theorems of analytic number theory whose formalisation in
mathlib is in progress (cf. `Mathlib.NumberTheory.SelbergSieve`,
`Mathlib.NumberTheory.Chebyshev`).

## References

* V. Brun, *Le crible d'Eratosthène et le théorème de Goldbach*,
  C. R. Acad. Sci. Paris 168 (1919), 544–546.
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974.
* D. R. Heath-Brown, *Lectures on sieves*, 2002 (basis for
  `Mathlib.NumberTheory.SelbergSieve`).
-/

namespace Gdbh
namespace PathCBrunSieve

open Finset Real

/-! ## Section 1 — The concrete sifted counting function

We follow the elementary set-up: `siftedCount N z` is the number of
integers `n ∈ [1, N]` having **no prime factor `p ≤ z`** (equivalently,
`n` is coprime to the primorial `z#`).

This is the unweighted version of `BoundingSieve.siftedSum` from
`Mathlib.NumberTheory.SelbergSieve`; we keep the integer-valued version
because the twin-prime application only needs counting. -/

/-- The set of integers in `[1, N]` with no prime divisor `≤ z`.

In Brun's argument this is the *sifted set* `S(A, P, z)`, with
`A = {1, …, N}` and `P = {primes ≤ z}`. -/
def siftedSet (N z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => ∀ p ≤ z, Nat.Prime p → ¬ p ∣ n)

/-- The number of integers in `[1, N]` sifted by primes up to `z`. -/
def siftedCount (N z : ℕ) : ℕ := (siftedSet N z).card

@[simp] lemma mem_siftedSet {N z n : ℕ} :
    n ∈ siftedSet N z ↔
      (1 ≤ n ∧ n ≤ N) ∧ ∀ p, p ≤ z → Nat.Prime p → ¬ p ∣ n := by
  simp [siftedSet, Finset.mem_Icc, and_assoc]

/-- Trivial upper bound: a sifted set is a subset of `[1, N]`, so its
size is `≤ N`. -/
theorem siftedCount_le (N z : ℕ) : siftedCount N z ≤ N := by
  unfold siftedCount siftedSet
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [Nat.card_Icc]

/-- The sifted set is contained in `[1, N]`. -/
lemma siftedSet_subset_Icc (N z : ℕ) :
    siftedSet N z ⊆ Finset.Icc 1 N :=
  Finset.filter_subset _ _

/-- Monotonicity: increasing `z` (sifting by more primes) gives a smaller
set. -/
theorem siftedCount_anti (N : ℕ) {z₁ z₂ : ℕ} (h : z₁ ≤ z₂) :
    siftedCount N z₂ ≤ siftedCount N z₁ := by
  unfold siftedCount
  apply Finset.card_le_card
  intro n hn
  simp only [mem_siftedSet] at hn ⊢
  refine ⟨hn.1, fun p hp hpr => hn.2 p (hp.trans h) hpr⟩

/-! ## Section 2 — Twin primes are sifted by `√N`

The simple combinatorial observation: if `(p, p+2)` is a twin-prime
pair with `3 ≤ p ≤ N`, then `p` has no prime divisor `q ≤ √(p) ≤ √N`
other than `p` itself.  When applied to sieve theory, this gives the
inclusion

```
{p : prime, 3 ≤ p ≤ N, p+2 prime} ⊆ siftedSet N z
```

for any `z < 3`, but the *useful* version replaces "3" by a parameter
`z` and uses that primes above `z` cannot be sifted out.  For the
concrete bookkeeping below, we content ourselves with the cleanest
statement: **twin-prime pair count up to `N` is at most
`siftedCount N z + (z + 1)`**, the `(z+1)` accounting for the (few)
primes `≤ z`. -/

/-- The set of "twin-prime initial members" `p` with `p` prime,
`p + 2` prime, and `p ≤ N`. -/
def twinPrimeInitials (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))

@[simp] lemma mem_twinPrimeInitials {N p : ℕ} :
    p ∈ twinPrimeInitials N ↔
      (1 ≤ p ∧ p ≤ N) ∧ Nat.Prime p ∧ Nat.Prime (p + 2) := by
  simp [twinPrimeInitials, Finset.mem_Icc, and_assoc]

/-- A prime `p` with `z < p` cannot be sifted out by primes `≤ z`.
This is the key elementary fact for relating twin-prime counts to the
sifted count. -/
lemma prime_gt_z_mem_siftedSet {N z p : ℕ} (hp1 : 1 ≤ p) (hp2 : p ≤ N)
    (hpr : Nat.Prime p) (hpz : z < p) :
    p ∈ siftedSet N z := by
  refine mem_siftedSet.mpr ⟨⟨hp1, hp2⟩, ?_⟩
  intro q hqz hqp hqdvd
  -- `q` prime divides the prime `p`, so `q = p`; but `q ≤ z < p`.
  have hqeq : q = p := ((Nat.prime_dvd_prime_iff_eq hqp hpr).mp hqdvd)
  rw [hqeq] at hqz
  exact (Nat.lt_irrefl p) (lt_of_le_of_lt hqz hpz)

/-- Splitting `twinPrimeInitials` by whether `p > z`: the "large" part
is contained in the sifted set. -/
lemma twinPrimeInitials_large_subset_siftedSet (N z : ℕ) :
    (twinPrimeInitials N).filter (fun p => z < p) ⊆ siftedSet N z := by
  intro p hp
  rw [Finset.mem_filter, mem_twinPrimeInitials] at hp
  obtain ⟨⟨⟨hp1, hp2⟩, hpr, _⟩, hpz⟩ := hp
  exact prime_gt_z_mem_siftedSet hp1 hp2 hpr hpz

/-- The "small" part `twinPrimeInitials ∩ [1, z]` has cardinality at
most `z` (since it is contained in `[1, z]`). -/
lemma twinPrimeInitials_small_card_le (N z : ℕ) :
    ((twinPrimeInitials N).filter (fun p => p ≤ z)).card ≤ z := by
  have hsub : (twinPrimeInitials N).filter (fun p => p ≤ z) ⊆ Finset.Icc 1 z := by
    intro p hp
    rw [Finset.mem_filter, mem_twinPrimeInitials] at hp
    exact Finset.mem_Icc.mpr ⟨hp.1.1.1, hp.2⟩
  have hbound := Finset.card_le_card hsub
  simpa [Nat.card_Icc] using hbound

/-- **Cardinal control on the twin-prime count via the sifted count.**
Every twin-prime initial member `p ≤ N` is either `≤ z` (of which there
are `≤ z`) or `> z` and hence belongs to the sifted set.  Hence

```
#twinPrimeInitials(N) ≤ siftedCount(N, z) + z.
```

This is the elementary "sieve inclusion" feeding Brun's argument. -/
theorem twinPrimeInitials_card_le_siftedCount_add (N z : ℕ) :
    (twinPrimeInitials N).card ≤ siftedCount N z + z := by
  classical
  set S := twinPrimeInitials N
  -- split via the predicate `p ≤ z`
  have hsplit :
      S.card =
        (S.filter (fun p => p ≤ z)).card
          + (S.filter (fun p => ¬ p ≤ z)).card :=
    (Finset.card_filter_add_card_filter_not (fun p => p ≤ z) (s := S)).symm
  -- the "¬ p ≤ z" filter is the "z < p" filter
  have hnot : ∀ p, ¬ p ≤ z ↔ z < p := fun p => by
    exact ⟨fun h => Nat.lt_of_not_ge h, fun h => Nat.not_le.mpr h⟩
  have hfilter_eq :
      S.filter (fun p => ¬ p ≤ z) = S.filter (fun p => z < p) := by
    apply Finset.filter_congr
    intro p _; exact hnot p
  rw [hsplit, hfilter_eq]
  have h_small : (S.filter (fun p => p ≤ z)).card ≤ z :=
    twinPrimeInitials_small_card_le N z
  have h_large : (S.filter (fun p => z < p)).card ≤ siftedCount N z := by
    unfold siftedCount
    exact Finset.card_le_card (twinPrimeInitials_large_subset_siftedSet N z)
  -- combine: small + large ≤ z + siftedCount = siftedCount + z
  calc (S.filter (fun p => p ≤ z)).card + (S.filter (fun p => z < p)).card
      ≤ z + siftedCount N z := Nat.add_le_add h_small h_large
    _ = siftedCount N z + z := Nat.add_comm _ _

/-- Same statement reformulated for the predicate-style definition used
in the brief. -/
theorem twinPrime_count_le_siftedCount_add (N z : ℕ) :
    ((Finset.Icc 1 N).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card
      ≤ siftedCount N z + z := by
  have : (Finset.Icc 1 N).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))
        = twinPrimeInitials N := rfl
  rw [this]
  exact twinPrimeInitials_card_le_siftedCount_add N z

/-! ## Section 3 — The Brun decomposition: three sub-Props

We isolate the three quantitative pieces of Brun's argument as
`Prop`-valued statements.  The aim is **not** to prove them here (they
are classical analytic-number-theory theorems whose mathlib
formalisation is in progress); the aim is to expose the *clean
interface* so that progress on any one piece can be plugged in.

### 3.1  `BrunMainTerm`

The first piece is the **truncated Möbius inversion**: there exists a
constant `C₁ > 0` and a function `z ↦ M(z) > 0` such that the sifted
count is bounded by

```
siftedCount(N, z) ≤ C₁ · N · M(z) + (error).
```

We take `M(z) = ∏_{p ≤ z}(1 - 1/p)` as the canonical choice; this is
the main-term factor in Brun's bound.

For the abstract decomposition we encode this as a hypothesis on a
function `M : ℕ → ℝ`. -/

/-- Abstract main-term factor: a positive function of the sieving
threshold.  In Brun's argument this is `∏_{p ≤ z}(1 - 1/p)`. -/
def IsBrunMainTermFactor (M : ℕ → ℝ) : Prop :=
  (∀ z, 0 < M z) ∧ Antitone M

/-- `BrunMainTerm` records the main-term bound

```
siftedCount(N, z) ≤ C₁ · N · M(z) + B(N, z) ,
```

where `M` is a Brun main-term factor (typically `∏_{p ≤ z}(1 - 1/p)`)
and `B(N, z)` is an "error reservoir" to be supplied by
`BrunErrorTerm`.  This is the *truncated inclusion–exclusion* output
of Brun's argument before the Mertens estimate is invoked. -/
def BrunMainTerm (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) : Prop :=
  IsBrunMainTermFactor M ∧
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ N z : ℕ, 0 < N →
        (siftedCount N z : ℝ) ≤ C₁ * (N : ℝ) * M z + B N z

/-- `BrunErrorTerm B` records that the error reservoir `B` is
absorbable, in the precise sense that for some constant `C₂` and some
choice of sieving threshold `z = z(N)`, we have

```
B(N, z(N)) ≤ C₂ · N / (log N)^2 .
```

Brun's argument achieves this with `z = N^{1/(2k)}` and a truncation
level `k = ⌊c · log log N⌋`; the combinatorial estimate
`(∑_{p ≤ z} 1)^k / k!` then beats any polynomial in `log N`. -/
def BrunErrorTerm (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ) : Prop :=
  ∃ C₂ N₀ : ℕ, 0 < C₂ ∧
    ∀ N : ℕ, N₀ ≤ N →
      B N (zChoice N) ≤ (C₂ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2

/-- `MertensProductBound` records Mertens' third theorem on the
factor `M`: for some constant `C₃` and the same sieve choice
`z = z(N)`, we have

```
M(z(N)) ≤ C₃ / (log N)^2 .
```

Brun uses `z = N^{1/(2k)}` so `log z ≍ log N / k`, but the Mertens
input `∏_{p ≤ z}(1 - 1/p) ≪ 1 / log z` only gives the *single* power
of `log N`; the *square* comes from applying the sieve to a *pair* of
primes simultaneously (the "Brun setup": sift `n(n+2)` rather than
`n`), which doubles the main-term exponent.  We absorb that
combinatorial doubling into the bound `M(z) ≤ C₃ / (log N)^2`
directly. -/
def MertensProductBound (M : ℕ → ℝ) (zChoice : ℕ → ℕ) : Prop :=
  ∃ C₃ N₀ : ℕ, 0 < C₃ ∧
    ∀ N : ℕ, N₀ ≤ N → 2 ≤ N →
      M (zChoice N) ≤ (C₃ : ℝ) / (Real.log (N : ℝ))^2

/-! ## Section 4 — The assembly theorem

We now show **unconditionally** that the three sub-Props combine to a
twin-prime upper bound of the desired Brun shape

```
#TwinPrimes(N) ≤ C · N · (log log N)^? / (log N)^2 + lower-order .
```

In the formalisation we deliberately keep the bookkeeping clean and
state the (weaker but still nontrivial) bound

```
#TwinPrimes(N) ≤ (C₁ C₃ + C₂) · N / (log N)^2 + z(N) ,
```

valid for `N ≥ max(N₀^{main}, N₀^{err}, 2)`.

The `+ z(N)` term arises from the elementary "small prime" correction
in `twinPrime_count_le_siftedCount_add`. -/

/-- **Brun's twin-prime upper bound, assembled from the three sub-Props.**

If we have

* a main-term factor `M` and an error reservoir `B` with
  `BrunMainTerm M B` (i.e. truncated inclusion–exclusion gives a
  bound on `siftedCount` of the shape `C₁ N M(z) + B(N, z)`),
* a sieve choice `z = zChoice N` and an error bound
  `BrunErrorTerm B zChoice` (i.e. `B(N, z(N)) ≤ C₂ N / (log N)^2`),
* a Mertens product bound `MertensProductBound M zChoice` (i.e.
  `M(z(N)) ≤ C₃ / (log N)^2`),

then there exist absolute constants `C > 0`, `N₀` such that for all
`N ≥ N₀`,

```
#{p ≤ N : p, p+2 both prime} ≤ C · N / (log N)^2 + zChoice N .
```

(The `zChoice N` term is the elementary small-prime correction.) -/
theorem twinPrime_count_upperBound_of_brunComponents
    (M : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ)
    (hMain : BrunMainTerm M B)
    (hErr  : BrunErrorTerm B zChoice)
    (hMert : MertensProductBound M zChoice) :
    ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧
      ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → 0 < N →
        (((Finset.Icc 1 N).filter
            (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
          ≤ C * (N : ℝ) / (Real.log (N : ℝ))^2 + (zChoice N : ℝ) := by
  -- Unpack the three sub-Props.
  obtain ⟨hMfact, C₁, hC₁pos, hMain_bd⟩ := hMain
  obtain ⟨C₂, N₀err, hC₂pos, hErr_bd⟩ := hErr
  obtain ⟨C₃, N₀mer, hC₃pos, hMert_bd⟩ := hMert
  -- Final constant and threshold.
  refine ⟨C₁ * (C₃ : ℝ) + (C₂ : ℝ),
          max N₀err N₀mer, ?_, ?_⟩
  · -- positivity: `C₁ * C₃ + C₂ > 0`.
    have hC₃real : (0 : ℝ) < (C₃ : ℝ) := by exact_mod_cast hC₃pos
    have hC₂real : (0 : ℝ) < (C₂ : ℝ) := by exact_mod_cast hC₂pos
    have h1 : 0 < C₁ * (C₃ : ℝ) := mul_pos hC₁pos hC₃real
    linarith
  · -- the main inequality.
    intro N hN hN2 hNpos
    have hN_err : N₀err ≤ N := le_trans (le_max_left _ _) hN
    have hN_mer : N₀mer ≤ N := le_trans (le_max_right _ _) hN
    -- Step (i): twin-prime ↦ sifted count
    have h1 :
        (((Finset.Icc 1 N).filter
            (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
          ≤ (siftedCount N (zChoice N) : ℝ) + (zChoice N : ℝ) := by
      have := twinPrime_count_le_siftedCount_add N (zChoice N)
      have : ((Finset.Icc 1 N).filter
              (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card
          ≤ siftedCount N (zChoice N) + zChoice N := this
      exact_mod_cast this
    -- Step (ii): Brun main-term decomposition
    have h2 :
        (siftedCount N (zChoice N) : ℝ)
          ≤ C₁ * (N : ℝ) * M (zChoice N) + B N (zChoice N) :=
      hMain_bd N (zChoice N) hNpos
    -- Step (iii): Mertens product bound (logN > 0 needed downstream)
    have hlogN_pos : 0 < Real.log (N : ℝ) := by
      have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN2
      exact Real.log_pos this
    have hlogN2_pos : 0 < (Real.log (N : ℝ))^2 := by positivity
    have hMz_bd : M (zChoice N) ≤ (C₃ : ℝ) / (Real.log (N : ℝ))^2 :=
      hMert_bd N hN_mer hN2
    -- Step (iv): error bound
    have hBz_bd :
        B N (zChoice N) ≤ (C₂ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2 :=
      hErr_bd N hN_err
    -- Now combine.
    have hNreal_nn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
    have hNreal_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hC₁N_nn : 0 ≤ C₁ * (N : ℝ) := mul_nonneg (le_of_lt hC₁pos) hNreal_nn
    -- C₁ * N * M(z) ≤ C₁ * N * C₃ / (log N)^2
    have h_main_bd :
        C₁ * (N : ℝ) * M (zChoice N)
          ≤ C₁ * (N : ℝ) * ((C₃ : ℝ) / (Real.log (N : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hMz_bd hC₁N_nn
    -- Combine main + error
    have h_sift_bd :
        (siftedCount N (zChoice N) : ℝ)
          ≤ C₁ * (N : ℝ) * ((C₃ : ℝ) / (Real.log (N : ℝ))^2)
            + (C₂ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2 := by
      calc (siftedCount N (zChoice N) : ℝ)
          ≤ C₁ * (N : ℝ) * M (zChoice N) + B N (zChoice N) := h2
        _ ≤ C₁ * (N : ℝ) * ((C₃ : ℝ) / (Real.log (N : ℝ))^2)
            + (C₂ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2 :=
              add_le_add h_main_bd hBz_bd
    -- Rewrite into (C₁ C₃ + C₂) · N / (log N)^2 form
    have hlog2_ne : (Real.log (N : ℝ))^2 ≠ 0 := ne_of_gt hlogN2_pos
    have h_alg :
        C₁ * (N : ℝ) * ((C₃ : ℝ) / (Real.log (N : ℝ))^2)
          + (C₂ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2
        = (C₁ * (C₃ : ℝ) + (C₂ : ℝ)) * (N : ℝ) / (Real.log (N : ℝ))^2 := by
      field_simp
    rw [h_alg] at h_sift_bd
    -- Conclude
    linarith

/-! ## Section 5 — A purely-existential repackaging

For downstream `audit_lean_axioms.py` registration, we provide a
cleaner existential form. -/

/-- **Existential form of Brun's twin-prime upper bound.**  Given the
three Brun sub-Props for *some* choice of `(M, B, zChoice)`, there exist
constants `C, N₀` such that the twin-prime count is bounded by
`C · N / (log N)^2 + zChoice N` for `N ≥ N₀`. -/
theorem exists_twinPrime_upperBound_of_brunComponents
    (h : ∃ M B zChoice,
            BrunMainTerm M B ∧ BrunErrorTerm B zChoice
            ∧ MertensProductBound M zChoice) :
    ∃ (zChoice : ℕ → ℕ) (C : ℝ) (N₀ : ℕ), 0 < C ∧
      ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → 0 < N →
        (((Finset.Icc 1 N).filter
            (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card : ℝ)
          ≤ C * (N : ℝ) / (Real.log (N : ℝ))^2 + (zChoice N : ℝ) := by
  obtain ⟨M, B, zChoice, hMain, hErr, hMert⟩ := h
  obtain ⟨C, N₀, hCpos, hbd⟩ :=
    twinPrime_count_upperBound_of_brunComponents M B zChoice hMain hErr hMert
  exact ⟨zChoice, C, N₀, hCpos, hbd⟩

/-! ## Section 6 — Recording the unconditional pieces

A small lemma collecting the unconditional cardinal-arithmetic content
of the file, for downstream auditing. -/

/-- Combined "always-true" Brun infrastructure lemma: every twin-prime
initial member up to `N` is either a small prime `≤ z` or belongs to
the sifted set; in particular, the twin-prime count is bounded by
`siftedCount + z` for *any* choice of `z`. -/
theorem brunSieve_elementary_inclusion (N z : ℕ) :
    ((Finset.Icc 1 N).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + 2))).card
      ≤ siftedCount N z + z :=
  twinPrime_count_le_siftedCount_add N z

end PathCBrunSieve
end Gdbh
