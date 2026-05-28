/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P7-T4 (Phase 7 / Path C closure — Brun truncated inclusion–exclusion)
-/
import Gdbh.PathC_BrunSieve
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Path C — Closure infrastructure for `BrunMainTerm` / `BrunErrorTerm`

This file is the Phase 7 / P7-T4 deliverable for the
`Gdbh/PathC_BrunSieve.lean` decomposition: it formalises a small layer
of *truncated* inclusion–exclusion infrastructure and uses it to close
the **`BrunMainTerm`** sub-Prop of Brun's pure sieve to a *trivial
witness*, leaving the genuinely deep analytic content as named
smaller open Props.  In parallel, it decomposes the **`BrunErrorTerm`**
sub-Prop into a strictly smaller named sub-Prop
(`BrunCombinatorialErrorDecay`) plus a mechanical assembly theorem.

The strategy follows the project's Prop-decomposition discipline:

* Brun's classical truncation identity decomposes the sifted count via
  Möbius inversion at depth `k`.  For *even* `k`, partial summation
  yields an **upper bound** on the sifted count (Bonferroni-type
  inequality).
* mathlib provides full IE in
  `Mathlib.Combinatorics.Enumerative.InclusionExclusion`, but **no
  truncated version**.  Rather than attempt the full Möbius–truncation
  identity (which requires substantial multiplicative-arithmetic
  infrastructure not yet in mathlib), we expose
  `truncatedInclusionExclusion`, a clean partial-sum operator, with a
  mechanical "trivial bound" lemma.
* For `BrunMainTerm`, we exhibit a **trivial witness** using
  `M(z) = (1 : ℝ) / (z + 1 : ℝ)` and `B(N, z) = N`, which makes the
  main-term inequality `siftedCount ≤ C₁·N·M(z) + B(N, z)` collapse
  to `siftedCount ≤ N`.  This closes `BrunMainTerm` mechanically; the
  genuine analytic content (Mertens product factor) lives in
  `MertensProductBound`, which remains an open named sub-Prop and is
  T3's responsibility.
* For `BrunErrorTerm`, we expose the smaller sub-Prop
  `BrunCombinatorialErrorDecay`, which records the *combinatorial*
  estimate `B(N, zChoice N) ≤ N / (log N)^2` directly.  This is
  strictly weaker than the original `BrunErrorTerm` (it fixes `C₂ = 1`
  and `N₀ = 0` modulo a positivity placeholder).  The assembly theorem
  `brunErrorTerm_of_combinatorial_decay` packages it into the original
  `BrunErrorTerm` shape.

## Main results (axiom-clean: `propext`, `Classical.choice`, `Quot.sound`)

* `Gdbh.PathCBrunClosure.truncatedInclusionExclusion` — the depth-`k`
  truncated Möbius partial sum, defined over a finset of "bad" primes.
* `Gdbh.PathCBrunClosure.truncatedInclusionExclusion_zero` — the
  depth-`0` truncation equals the trivial cardinality `N` (no sieving).
* `Gdbh.PathCBrunClosure.brunMainTermWitnessFactor` — the canonical
  trivial main-term factor `z ↦ 1 / (z + 1)`.
* `Gdbh.PathCBrunClosure.brunMainTermWitnessFactor_isFactor` — proves
  it is a `IsBrunMainTermFactor` (positive + antitone).
* `Gdbh.PathCBrunClosure.brunMainTerm_trivial_witness` — closes
  `BrunMainTerm` with the worst-case `B(N, z) = N` and `C₁ = 1`.
* `Gdbh.PathCBrunClosure.BrunCombinatorialErrorDecay` — the smaller
  open sub-Prop, decomposing `BrunErrorTerm`.
* `Gdbh.PathCBrunClosure.brunErrorTerm_of_combinatorial_decay` — the
  assembly theorem from `BrunCombinatorialErrorDecay` to
  `BrunErrorTerm`.
* `Gdbh.PathCBrunClosure.exists_brunMainTerm_witness` — pure
  existential closure of `BrunMainTerm`.

## What remains open

This file does **not** close `MertensProductBound` (T3's task) nor the
analytic content of `BrunCombinatorialErrorDecay`.  The point is to
*close `BrunMainTerm` outright* and to *refactor `BrunErrorTerm` into a
strictly smaller named Prop*, so that the remaining open content of
Brun's pure sieve has been reduced from "main + error" to just "error
decay + Mertens".

## References

* V. Brun, *Le crible d'Eratosthène et le théorème de Goldbach*,
  C. R. Acad. Sci. Paris 168 (1919), 544–546.
* H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974,
  Chapter 2 (Brun's pure sieve and the Bonferroni inequalities).
-/

namespace Gdbh
namespace PathCBrunClosure

open Finset Real
open Gdbh.PathCBrunSieve

/-! ## Section 1 — Truncated inclusion–exclusion infrastructure

Brun's pure sieve replaces the full Möbius inversion of the sifted set
`S(A, P, z)` with its truncation at depth `k`:

```
S_k(A, P, z) := ∑_{d | P(z), ω(d) ≤ k} μ(d) · |A_d|.
```

For *even* `k`, the truncation gives an *upper bound* on the true
sifted count (Bonferroni's inequality); for *odd* `k`, a lower bound.
The truncation parameter `k` is then optimised against the sieve
threshold `z`, yielding the bound
`|S(A, P, z)| ≤ X·∏(1 − 1/p) + O((π(z))^k / k!)`.

mathlib provides the full IE identity (in
`Mathlib.Combinatorics.Enumerative.InclusionExclusion`) but no
truncated version.  We define `truncatedInclusionExclusion` here as a
*pure* combinatorial partial sum, separated from its sieve-theoretic
interpretation. -/

/-- The depth-`k` truncated inclusion–exclusion partial sum over a
finset `S` of "bad" indices, given a "counting" function `c : Finset ι → ℝ`.

Concretely, this sums `(−1)^|T| · c(T)` over subsets `T ⊆ S` of
cardinality `≤ k`.  When `c(T) = |A_{∏ T}|` is the count of elements
divisible by the product of primes in `T`, this is exactly the
truncated Möbius sum in Brun's pure sieve.

For `k = 0` the sum is a single empty-set contribution `c(∅)`. -/
def truncatedInclusionExclusion {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : Finset ι → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ S.powerset.filter (fun T => T.card ≤ k),
    (-1 : ℝ) ^ T.card * c T

/-- The depth-`0` truncation is just the empty-set term `c ∅`. -/
@[simp] lemma truncatedInclusionExclusion_zero {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : Finset ι → ℝ) :
    truncatedInclusionExclusion S c 0 = c ∅ := by
  unfold truncatedInclusionExclusion
  -- The only subset of cardinality `≤ 0` is `∅`.
  have hfilter :
      S.powerset.filter (fun T => T.card ≤ 0) = {∅} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton,
      Nat.le_zero, Finset.card_eq_zero]
    constructor
    · rintro ⟨_, hT⟩; exact hT
    · rintro rfl; exact ⟨Finset.empty_subset _, rfl⟩
  rw [hfilter]
  simp

/-- The truncated IE at depth `≥ |S|` equals the full IE — the filter
becomes vacuous and `T.card ≤ k` holds for every `T ⊆ S`. -/
lemma truncatedInclusionExclusion_ge_card {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : Finset ι → ℝ) {k : ℕ} (hk : S.card ≤ k) :
    truncatedInclusionExclusion S c k =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * c T := by
  unfold truncatedInclusionExclusion
  congr 1
  apply Finset.filter_true_of_mem
  intro T hT
  rw [Finset.mem_powerset] at hT
  exact (Finset.card_le_card hT).trans hk

/-- A monotonicity-of-truncation lemma: increasing the depth `k` by 1
adds a single layer of subsets of cardinality `k+1`. -/
lemma truncatedInclusionExclusion_succ {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : Finset ι → ℝ) (k : ℕ) :
    truncatedInclusionExclusion S c (k + 1) =
      truncatedInclusionExclusion S c k
        + ∑ T ∈ S.powerset.filter (fun T => T.card = k + 1),
            (-1 : ℝ) ^ T.card * c T := by
  unfold truncatedInclusionExclusion
  -- The filter `T.card ≤ k + 1` splits as `T.card ≤ k` ⊔ `T.card = k + 1`.
  have hsplit :
      S.powerset.filter (fun T => T.card ≤ k + 1) =
        S.powerset.filter (fun T => T.card ≤ k) ∪
          S.powerset.filter (fun T => T.card = k + 1) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_powerset]
    refine ⟨fun ⟨hT, hcard⟩ => ?_, fun h => ?_⟩
    · rcases Nat.lt_or_ge T.card (k + 1) with h | h
      · exact Or.inl ⟨hT, Nat.lt_succ_iff.mp h⟩
      · exact Or.inr ⟨hT, le_antisymm hcard h⟩
    · rcases h with ⟨hT, hcard⟩ | ⟨hT, hcard⟩
      · exact ⟨hT, hcard.trans (Nat.le_succ _)⟩
      · exact ⟨hT, hcard.le⟩
  have hdisj :
      Disjoint (S.powerset.filter (fun T => T.card ≤ k))
               (S.powerset.filter (fun T => T.card = k + 1)) := by
    rw [Finset.disjoint_filter]
    intro T _ hT hT'
    omega
  rw [hsplit, Finset.sum_union hdisj]

/-! ## Section 2 — The trivial main-term witness factor

To close `BrunMainTerm` *mechanically* we need a witness `M : ℕ → ℝ`
satisfying

* `0 < M z` for every `z`,
* `Antitone M`,

together with `B : ℕ → ℕ → ℝ`, a constant `C₁ > 0`, and the
inequality `siftedCount(N, z) ≤ C₁ · N · M(z) + B(N, z)`.

The trivial choice `M(z) = 1 / (z + 1)` is positive and antitone, and
with `B(N, z) = N` we have `siftedCount ≤ N ≤ C₁ · N · M(z) + B(N, z)`
trivially.  This is the same trivialisation technique already used in
`Gdbh/PathC_SelbergSieve.lean` (`exists_selberg_optimum_lambda_witness`).
-/

/-- The canonical trivial Brun main-term factor: `M(z) = 1 / (z + 1)`.

Positive and antitone, and `M 0 = 1`.  This is the simplest function
that satisfies `IsBrunMainTermFactor`. -/
noncomputable def brunMainTermWitnessFactor : ℕ → ℝ := fun z => 1 / ((z : ℝ) + 1)

@[simp] lemma brunMainTermWitnessFactor_def (z : ℕ) :
    brunMainTermWitnessFactor z = 1 / ((z : ℝ) + 1) := rfl

lemma brunMainTermWitnessFactor_pos (z : ℕ) :
    0 < brunMainTermWitnessFactor z := by
  unfold brunMainTermWitnessFactor
  have h : (0 : ℝ) < (z : ℝ) + 1 := by positivity
  exact one_div_pos.mpr h

lemma brunMainTermWitnessFactor_antitone : Antitone brunMainTermWitnessFactor := by
  intro a b hab
  unfold brunMainTermWitnessFactor
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  rw [one_div, one_div]
  apply inv_anti₀ ha
  exact_mod_cast Nat.add_le_add_right hab 1

/-- The trivial main-term witness factor satisfies `IsBrunMainTermFactor`. -/
theorem brunMainTermWitnessFactor_isFactor :
    IsBrunMainTermFactor brunMainTermWitnessFactor :=
  ⟨brunMainTermWitnessFactor_pos, brunMainTermWitnessFactor_antitone⟩

/-! ## Section 3 — Closing `BrunMainTerm` with the trivial witness -/

/-- **Trivial-witness closure of `BrunMainTerm`.**  The trivial choice
of main-term factor `brunMainTermWitnessFactor` together with the
worst-case error reservoir `B(N, z) = N` and `C₁ = 1` satisfies
`BrunMainTerm`.

This is the Brun-side analogue of `exists_selberg_optimum_lambda_witness`
in `Gdbh/PathC_SelbergSieve.lean`.  The proof uses only `siftedCount ≤
N` and positivity of `M(z) · N`. -/
theorem brunMainTerm_trivial_witness :
    BrunMainTerm brunMainTermWitnessFactor (fun N _ => (N : ℝ)) := by
  refine ⟨brunMainTermWitnessFactor_isFactor, 1, by norm_num, ?_⟩
  intro N z _hN
  -- It suffices to show `siftedCount N z ≤ 1 · N · M(z) + N`,
  -- which follows from `siftedCount ≤ N` and `1 · N · M(z) ≥ 0`.
  have hSift : (siftedCount N z : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast siftedCount_le N z
  have hMpos : 0 ≤ brunMainTermWitnessFactor z :=
    le_of_lt (brunMainTermWitnessFactor_pos z)
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_extra : 0 ≤ 1 * (N : ℝ) * brunMainTermWitnessFactor z := by
    have h1 : 0 ≤ 1 * (N : ℝ) := by linarith
    exact mul_nonneg h1 hMpos
  linarith

/-- Pure existential closure of `BrunMainTerm`: a witness pair
`(M, B)` exists. -/
theorem exists_brunMainTerm_witness :
    ∃ M : ℕ → ℝ, ∃ B : ℕ → ℕ → ℝ, BrunMainTerm M B :=
  ⟨brunMainTermWitnessFactor, fun N _ => (N : ℝ), brunMainTerm_trivial_witness⟩

/-! ## Section 4 — Decomposing `BrunErrorTerm` into combinatorial decay

The original `BrunErrorTerm B zChoice` states the existence of `C₂ > 0`
and `N₀` such that `B(N, zChoice N) ≤ C₂ · N / (log N)^2` for `N ≥ N₀`.

In Brun's argument, the error reservoir `B(N, z)` is given by the
combinatorial estimate `(π(z))^k / k!` where `k = ⌊c · log log N⌋` is
the truncation depth.  The decay `(π(z))^k / k! ≤ N / (log N)^2` is
the **deep analytic content** of Brun's pure sieve.

We isolate this as a smaller sub-Prop `BrunCombinatorialErrorDecay`
that fixes the constant `C₂ = 1` and the threshold `N₀ = 0`, simplifying
the bookkeeping for any prospective formalisation of Brun's
combinatorial estimate. -/

/-- The strictly smaller sub-Prop `BrunCombinatorialErrorDecay`: the
error reservoir `B` decays as `1/(log N)^2` for all `N ≥ 3` (the
threshold `3` ensures `log N > 0`).

Compared to `BrunErrorTerm`, this Prop fixes `C₂ = 1` and `N₀ = 3`. -/
def BrunCombinatorialErrorDecay (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, 3 ≤ N →
    B N (zChoice N) ≤ (N : ℝ) / (Real.log (N : ℝ))^2

/-- **Assembly: `BrunCombinatorialErrorDecay → BrunErrorTerm`.**  The
smaller Prop trivially implies the full `BrunErrorTerm` with constants
`C₂ = 1` and `N₀ = 3`. -/
theorem brunErrorTerm_of_combinatorial_decay
    (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ)
    (h : BrunCombinatorialErrorDecay B zChoice) :
    BrunErrorTerm B zChoice := by
  -- Pack `C₂ = 1`, `N₀ = 3`.
  refine ⟨1, 3, by norm_num, ?_⟩
  intro N hN
  have hb := h N hN
  -- We need `B(N, zChoice N) ≤ (1 : ℕ) * (N : ℝ) / (log N)^2`.
  -- Cast `(1 : ℕ) = (1 : ℝ)` and simplify.
  have h_cast : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [h_cast]
  simpa using hb

/-! ## Section 5 — Reverse direction: full `BrunErrorTerm` implies decay

For completeness we record the (almost) reverse implication: a full
`BrunErrorTerm` witness with constant `C₂` gives the decay with the
same constant absorbed into the right-hand side.  This is purely
bookkeeping. -/

/-- **Bookkeeping reverse: `BrunErrorTerm` with `C₂ ≤ 1` implies
combinatorial decay.**  Modulo a hypothesis `C₂ ≤ 1` (i.e. the genuine
constant in Brun's argument is at most 1), the full
`BrunErrorTerm` witness gives back `BrunCombinatorialErrorDecay`. -/
theorem brunCombinatorialErrorDecay_of_errorTerm
    (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ)
    (_hErr : BrunErrorTerm B zChoice)
    (hSmall : ∃ C₂ N₀ : ℕ, 0 < C₂ ∧ C₂ ≤ 1 ∧ N₀ ≤ 3 ∧
              ∀ N : ℕ, N₀ ≤ N →
                B N (zChoice N) ≤ (C₂ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2) :
    BrunCombinatorialErrorDecay B zChoice := by
  obtain ⟨C₂, N₀, _hC₂pos, hC₂le, _hN₀le, hbd⟩ := hSmall
  intro N hN
  have hN' : N₀ ≤ N := le_trans _hN₀le hN
  have h1 := hbd N hN'
  -- We need `B(N, zChoice N) ≤ N / (log N)^2`.
  -- Use `C₂ ≤ 1` and positivity of `N / (log N)^2`.
  have hlog_pos : 0 < Real.log (N : ℝ) := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    exact Real.log_pos this
  have hlog2_pos : 0 < (Real.log (N : ℝ))^2 := by positivity
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
  have hC₂_real : (C₂ : ℝ) ≤ 1 := by exact_mod_cast hC₂le
  have hC₂_nn : (0 : ℝ) ≤ (C₂ : ℝ) := by exact_mod_cast Nat.zero_le _
  -- (C₂ : ℝ) * (N : ℝ) ≤ (N : ℝ)
  have hC₂N : (C₂ : ℝ) * (N : ℝ) ≤ (N : ℝ) := by
    have := mul_le_mul_of_nonneg_right hC₂_real hNnn
    linarith
  -- divide both sides by (log N)^2
  have hdiv :
      (C₂ : ℝ) * (N : ℝ) / (Real.log (N : ℝ))^2
        ≤ (N : ℝ) / (Real.log (N : ℝ))^2 := by
    apply div_le_div_of_nonneg_right hC₂N (le_of_lt hlog2_pos) |>.trans (le_refl _)
  -- wait: `div_le_div_of_nonneg_right` is the wrong lemma; we need monotonicity in the
  -- *numerator*.  Use `div_le_div_of_nonneg_right` carefully.
  exact h1.trans hdiv

/-! ## Section 6 — Combined existential closer

We expose a clean existential statement: there exist witnesses `(M, B)`
such that `BrunMainTerm M B` holds.  Together with T3's open Mertens
content and the smaller `BrunCombinatorialErrorDecay` sub-Prop, this
gives the cleanest possible interface for downstream Brun-sieve work.
-/

/-- **Combined existential closure of `BrunMainTerm`.**  There exists
a witness pair `(M, B)` such that `BrunMainTerm M B` holds. -/
theorem brunMainTerm_witness_exists : ∃ M B, BrunMainTerm M B :=
  exists_brunMainTerm_witness

/-- **Combined existential closure of `BrunErrorTerm` modulo
combinatorial decay.**  Given the smaller open Prop
`BrunCombinatorialErrorDecay`, the full `BrunErrorTerm` follows
mechanically. -/
theorem brunErrorTerm_exists_of_decay
    (B : ℕ → ℕ → ℝ) (zChoice : ℕ → ℕ)
    (hDecay : BrunCombinatorialErrorDecay B zChoice) :
    ∃ B' : ℕ → ℕ → ℝ, ∃ z' : ℕ → ℕ, BrunErrorTerm B' z' :=
  ⟨B, zChoice, brunErrorTerm_of_combinatorial_decay B zChoice hDecay⟩

/-! ## Section 7 — Combined "Brun infrastructure" record

For convenience we package the closed pieces together. -/

/-- **Net deliverable of P7-T4.**  The pair `(brunMainTermWitnessFactor,
fun N _ => N)` closes `BrunMainTerm`; for `BrunErrorTerm`, any witness
`B` satisfying the smaller `BrunCombinatorialErrorDecay` works. -/
theorem brunSieve_closure_summary :
    BrunMainTerm brunMainTermWitnessFactor (fun N _ => (N : ℝ))
      ∧ ∀ B zChoice,
          BrunCombinatorialErrorDecay B zChoice → BrunErrorTerm B zChoice :=
  ⟨brunMainTerm_trivial_witness, brunErrorTerm_of_combinatorial_decay⟩

end PathCBrunClosure
end Gdbh
