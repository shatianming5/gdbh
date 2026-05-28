/-
Copyright (c) 2026 Goldbach Project Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: P14-T1 (Phase 14 / deepest mathlib-achievable closure — Prime-power tail)
-/
import Gdbh.PathC_MertensFirstProof
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Path C — Prime-Power Tail Bound (P14-T1)

This file is the **P14-T1 deliverable** of Phase 14 (deepest
mathlib-achievable closures).  Its target is the named open Prop
`Gdbh.PathCMertensFirstProof.PrimePowerTailBound`:

```
∃ B' : ℝ, ∀ N : ℕ,
  Σ_{n ∈ Icc 1 N, IsPrimePow n, ¬n.Prime} Λ(n) / n  ≤  B' .
```

## Strategy

For each `n` in the filter, `n = p^k` with `p` prime and `k ≥ 2`,
hence `Λ(n) = log p` and `Λ(n)/n = log p / p^k`.  Inject the filter
into `(Icc 2 N) ×ˢ (Ico 2 (N+1))` via `n ↦ (minFac n, factorization n)`,
then dominate term-wise by the larger rectangle, split, bound each
inner sum by a geometric series (≤ `2/p²` since `p ≥ 2`), and finally
bound by `2 · ∑' n, log n / n²` (summable via `log n ≤ 2√n`).

## Result

* `primePowerTailBound` — closes `PrimePowerTailBound` unconditionally
  (axiom-clean: `[Classical.choice, Quot.sound, propext]`).
-/

namespace Gdbh
namespace PathCPrimePowerTail

open Real Finset
open Gdbh.PathCMertensFirstProof
open ArithmeticFunction

/-! ## Section 1 — Summability of `log n / n²` -/

/-- `Real.log n ≤ 2 √n` for all real `n ≥ 0`. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hsqrt_nn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  -- log x = 2 * log √x ≤ 2 * √x (using log_le_self at √x).
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx]; ring
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x := Real.log_le_self hsqrt_nn
  linarith

/-- The function `n ↦ log n / n²` is summable over ℕ. -/
lemma summable_log_div_sq :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
  -- Dominate by `2 / n^(3/2)`, which is summable.
  have hps : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2)) := by
    rw [summable_one_div_nat_rpow]; norm_num
  have hg : Summable (fun n : ℕ => 2 * ((1 : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2))) :=
    hps.mul_left 2
  refine Summable.of_nonneg_of_le ?_ ?_ hg
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    · have : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
      positivity
  · intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0; simp
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
    have hlog_nn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    -- log n ≤ 2 √n.
    have hlog_le : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) :=
      log_le_two_sqrt hnpos.le
    -- Reduce to: 2 √n / n² ≤ 2 / n^(3/2).
    -- Both sides equal 2/n^(3/2) actually; use equality.
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    -- Use n^(3/2) = √n · n.
    have hrpow : (n : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt (n : ℝ) * (n : ℝ) := by
      rw [Real.sqrt_eq_rpow,
          show ((3 : ℝ) / 2) = (1/2 : ℝ) + 1 by norm_num,
          Real.rpow_add hnpos, Real.rpow_one]
    -- Now we want: log n / n² ≤ 2 / n^(3/2).
    -- I.e., log n · n^(3/2) ≤ 2 · n².
    -- I.e., log n · √n · n ≤ 2 · n².
    -- I.e., log n · √n ≤ 2 n (divide by n > 0).
    -- Since log n ≤ 2 √n and √n · √n = n, we have log n · √n ≤ 2 √n · √n = 2 n. ✓
    -- Compute.
    have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hrpowpos : (0 : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [hrpow]; exact mul_pos hsqrt_pos hnpos
    -- 2 * (1 / x) = 2 / x.
    have hrhs : (2 : ℝ) * (1 / (n : ℝ) ^ ((3 : ℝ) / 2))
              = 2 / (n : ℝ) ^ ((3 : ℝ) / 2) := by ring
    rw [hrhs]
    rw [div_le_div_iff₀ hn2pos hrpowpos]
    -- Want: log n * n^(3/2) ≤ 2 * n^2.
    rw [hrpow]
    -- log n * (√n * n) ≤ 2 * n^2
    have hsqrt_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
      Real.mul_self_sqrt hnpos.le
    have hnn : (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) := sq (n : ℝ)
    calc Real.log (n : ℝ) * (Real.sqrt (n : ℝ) * (n : ℝ))
        = (Real.log (n : ℝ) * Real.sqrt (n : ℝ)) * (n : ℝ) := by ring
      _ ≤ (2 * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) * (n : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hnpos.le
            calc Real.log (n : ℝ) * Real.sqrt (n : ℝ)
                ≤ (2 * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) :=
                  mul_le_mul_of_nonneg_right hlog_le (Real.sqrt_nonneg _)
              _ = 2 * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by ring
      _ = 2 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) * (n : ℝ) := by ring
      _ = 2 * (n : ℝ) * (n : ℝ) := by rw [hsqrt_sq]
      _ = 2 * (n : ℝ) ^ 2 := by ring

/-- The total mass `2 * ∑' n, log n / n²`, used as the uniform bound `B'`. -/
noncomputable def B' : ℝ := 2 * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2

/-! ## Section 2 — Geometric tail bound -/

/-- For `p : ℝ` with `2 ≤ p`, the geometric tail
`∑_{k ∈ Ico 2 (N+1)} (1/p)^k` is bounded by `2/p²`. -/
lemma geom_tail_bound {p : ℝ} (hp : 2 ≤ p) (N : ℕ) :
    ∑ k ∈ Ico 2 (N + 1), (1 / p) ^ k ≤ 2 / p ^ 2 := by
  have hp_pos : 0 < p := by linarith
  have hinv_pos : 0 < 1 / p := by positivity
  have hinv_lt : 1 / p < 1 := by
    rw [div_lt_one hp_pos]; linarith
  have hinv_nn : 0 ≤ 1 / p := hinv_pos.le
  -- Use geom_sum_Ico_le_of_lt_one: ∑ i ∈ Ico m n, x^i ≤ x^m / (1 - x).
  have hbound := geom_sum_Ico_le_of_lt_one (m := 2) (n := N + 1) hinv_nn hinv_lt
  -- (1/p)^2 / (1 - 1/p) = 1/(p^2 (1 - 1/p)) = 1/(p^2 - p).
  -- (1/p)^2 / (1 - 1/p) ≤ 2/p^2 since 1 - 1/p ≥ 1/2 (because p ≥ 2).
  refine hbound.trans ?_
  -- Want: (1/p)^2 / (1 - 1/p) ≤ 2/p^2.
  have h1mp : (1 / 2 : ℝ) ≤ 1 - 1 / p := by
    have : 1 / p ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left _ (by norm_num : (0 : ℝ) < 2) hp
      norm_num
    linarith
  have h1mp_pos : 0 < 1 - 1 / p := by linarith
  rw [div_le_div_iff₀ h1mp_pos (by positivity : (0 : ℝ) < p ^ 2)]
  -- Want: (1/p)^2 · p^2 ≤ 2 · (1 - 1/p).
  have hp_ne : p ≠ 0 := by linarith
  have hsq : (1 / p) ^ 2 * p ^ 2 = 1 := by
    field_simp
  rw [hsq]
  -- 1 ≤ 2 * (1 - 1/p)
  -- 2/p ≤ 1
  rw [mul_sub, mul_one]
  have h2p : 2 / p ≤ 1 := by
    rw [div_le_one hp_pos]; linarith
  -- We want 1 ≤ 2 - 2 * (1/p). Rewrite 2 * (1/p) = 2/p.
  have h2p_eq : 2 * (1 / p) = 2 / p := by ring
  rw [h2p_eq]
  linarith

/-! ## Section 3 — Reindex the filter sum via `(p, k)` injection -/

/-- The injection `n ↦ (minFac n, factorization n (minFac n))` is
injective on the set of prime powers. -/
lemma injOn_minFac_fac (N : ℕ) :
    Set.InjOn (fun n : ℕ => (n.minFac, n.factorization n.minFac))
      ((Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)) := by
  intro a ha b hb hab
  rcases Finset.mem_filter.mp ha with ⟨_, hpp_a, _⟩
  rcases Finset.mem_filter.mp hb with ⟨_, hpp_b, _⟩
  -- Use that n = (minFac n)^(factorization n (minFac n)) for prime powers.
  have rec_a : a.minFac ^ a.factorization a.minFac = a :=
    hpp_a.minFac_pow_factorization_eq
  have rec_b : b.minFac ^ b.factorization b.minFac = b :=
    hpp_b.minFac_pow_factorization_eq
  rw [Prod.mk.injEq] at hab
  obtain ⟨hp_eq, hk_eq⟩ := hab
  -- a = a.minFac ^ a.factorization a.minFac = b.minFac ^ b.factorization b.minFac = b.
  have hkey : a.minFac ^ a.factorization a.minFac
       = b.minFac ^ b.factorization b.minFac := by
    rw [hk_eq, hp_eq]
  rw [rec_a] at hkey
  rw [hkey, rec_b]

/-- The image of the filter under the `(minFac, factorization)` map. -/
lemma image_subset_rectangle (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).image
        (fun n => (n.minFac, n.factorization n.minFac))
      ⊆ (Finset.Icc 2 N) ×ˢ (Finset.Ico 2 (N + 1)) := by
  intro pk hpk
  rcases Finset.mem_image.mp hpk with ⟨n, hn, hn_eq⟩
  rcases Finset.mem_filter.mp hn with ⟨hn_mem, hpp, hnp⟩
  rcases Finset.mem_Icc.mp hn_mem with ⟨hn1, hnN⟩
  -- n = minFac(n) ^ factorization(n)(minFac n).
  have hrec : n.minFac ^ n.factorization n.minFac = n :=
    hpp.minFac_pow_factorization_eq
  -- n ≥ 2 since n is a prime power.
  have hn_ge_two : 2 ≤ n := hpp.two_le
  have hn_ne_one : n ≠ 1 := by omega
  have hn_ne_zero : n ≠ 0 := by omega
  -- minFac n is prime.
  have hmF_prime : (n.minFac).Prime := Nat.minFac_prime hn_ne_one
  -- The exponent factorization n (minFac n) ≥ 2 (since n is not prime).
  have hk_pos : 0 < n.factorization n.minFac := by
    exact hmF_prime.factorization_pos_of_dvd hn_ne_zero (Nat.minFac_dvd n)
  have hk_ge_two : 2 ≤ n.factorization n.minFac := by
    rcases Nat.lt_or_ge (n.factorization n.minFac) 2 with hlt | hge
    · exfalso
      -- factorization is 0 or 1. Can't be 0. So 1.
      interval_cases (n.factorization n.minFac)
      -- case 0: contradiction with hk_pos.
      -- case 1: n = minFac^1 = minFac is prime, contradiction with hnp.
      have hn_eq : n = n.minFac := by
        have := hrec
        simp at this
        exact this.symm
      rw [hn_eq] at hnp
      exact hnp hmF_prime
    · exact hge
  -- p = minFac n ∈ Icc 2 N: p ≥ 2 since p prime, p ≤ n ≤ N.
  have hp_ge_two : 2 ≤ n.minFac := hmF_prime.two_le
  have hn_pos : 0 < n := by omega
  have hp_le_N : n.minFac ≤ N := le_trans (Nat.minFac_le hn_pos) hnN
  -- k ≤ N: k ≤ n (since 2^k ≤ p^k = n) and n ≤ N.
  have hk_le_N : n.factorization n.minFac ≤ N := by
    have : n.factorization n.minFac ≤ n := by
      have hpk : n.minFac ^ n.factorization n.minFac = n := hrec
      have : n.factorization n.minFac < n.minFac ^ n.factorization n.minFac :=
        Nat.lt_pow_self hp_ge_two
      rw [hpk] at this
      omega
    omega
  -- Assemble.
  rw [← hn_eq]
  rw [Finset.mem_product]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_Icc]; exact ⟨hp_ge_two, hp_le_N⟩
  · rw [Finset.mem_Ico]; exact ⟨hk_ge_two, by omega⟩

/-! ## Section 4 — Main result -/

/-- **P14-T1 main theorem**: `PrimePowerTailBound` is provable
unconditionally. -/
theorem primePowerTailBound : PrimePowerTailBound := by
  classical
  refine ⟨B', ?_⟩
  intro N
  set F := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) with hF_def
  set φ : ℕ → ℕ × ℕ := fun n => (n.minFac, n.factorization n.minFac) with hφ_def
  -- Step 1: rewrite Λ(n)/n = log(minFac n)/n on the filter (and = log p / p^k).
  have hstep1 :
      (∑ n ∈ F, (Λ n / (n : ℝ)))
        = ∑ n ∈ F, (Real.log (n.minFac : ℝ) / (n : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨_, hpp, _⟩
    rw [vonMangoldt_apply, if_pos hpp]
  -- Step 2: change variable n ↦ (n.minFac, n.factorization n.minFac).
  -- ∑ n ∈ F, log(n.minFac)/n = ∑ (p,k) ∈ φ '' F, log p / p^k.
  have hstep2 :
      (∑ n ∈ F, (Real.log (n.minFac : ℝ) / (n : ℝ)))
        = ∑ pk ∈ F.image φ,
            (Real.log (pk.1 : ℝ) / ((pk.1 : ℝ) ^ pk.2)) := by
    rw [Finset.sum_image (fun a ha b hb hab =>
      injOn_minFac_fac N ha hb hab)]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨_, hpp, _⟩
    -- n = (minFac n)^(factorization n (minFac n))
    have hrec : n.minFac ^ n.factorization n.minFac = n :=
      hpp.minFac_pow_factorization_eq
    -- φ n = (n.minFac, n.factorization n.minFac).
    show Real.log (n.minFac : ℝ) / (n : ℝ)
       = Real.log ((φ n).1 : ℝ) / (((φ n).1 : ℝ) ^ (φ n).2)
    simp only [hφ_def]
    -- (n.minFac : ℝ) ^ factorization = (n : ℝ).
    have hcast : ((n.minFac : ℝ)) ^ n.factorization n.minFac = (n : ℝ) := by
      exact_mod_cast hrec
    rw [hcast]
  -- Step 3: F.image φ ⊆ (Icc 2 N) ×ˢ (Ico 2 (N+1)).
  have himg_sub : F.image φ ⊆ (Finset.Icc 2 N) ×ˢ (Finset.Ico 2 (N + 1)) := by
    intro pk hpk
    exact image_subset_rectangle N hpk
  -- Step 4: dominate by larger sum (all terms nonneg).
  have hstep4 :
      (∑ pk ∈ F.image φ,
          (Real.log (pk.1 : ℝ) / ((pk.1 : ℝ) ^ pk.2)))
        ≤ ∑ pk ∈ (Finset.Icc 2 N) ×ˢ (Finset.Ico 2 (N + 1)),
            (Real.log (pk.1 : ℝ) / ((pk.1 : ℝ) ^ pk.2)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg himg_sub ?_
    intro pk hpk _
    rcases Finset.mem_product.mp hpk with ⟨hp, hk⟩
    rcases Finset.mem_Icc.mp hp with ⟨hp2, _⟩
    have hp_pos : (0 : ℝ) < (pk.1 : ℝ) := by
      have : 2 ≤ pk.1 := hp2
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) this
    apply div_nonneg
    · exact Real.log_natCast_nonneg _
    · positivity
  -- Step 5: split product sum: ∑_{(p,k)} = ∑_p ∑_k.
  have hstep5 :
      (∑ pk ∈ (Finset.Icc 2 N) ×ˢ (Finset.Ico 2 (N + 1)),
          (Real.log (pk.1 : ℝ) / ((pk.1 : ℝ) ^ pk.2)))
        = ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Ico 2 (N + 1),
            (Real.log (p : ℝ) / ((p : ℝ) ^ k)) := by
    rw [← Finset.sum_product']
  -- Step 6: factor out log p, use geom_tail_bound.
  have hstep6 :
      (∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Ico 2 (N + 1),
          (Real.log (p : ℝ) / ((p : ℝ) ^ k)))
        ≤ ∑ p ∈ Finset.Icc 2 N, (2 * Real.log (p : ℝ) / ((p : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro p hp
    rcases Finset.mem_Icc.mp hp with ⟨hp2, _⟩
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hp2
    have hp_ge : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg _
    -- ∑_k log p / p^k = log p · ∑_k (1/p)^k.
    have hfactor :
        (∑ k ∈ Finset.Ico 2 (N + 1), (Real.log (p : ℝ) / ((p : ℝ) ^ k)))
          = Real.log (p : ℝ) * ∑ k ∈ Finset.Ico 2 (N + 1), ((1 / (p : ℝ)) ^ k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have : ((1 : ℝ) / (p : ℝ)) ^ k = 1 / (p : ℝ) ^ k := by rw [div_pow, one_pow]
      rw [this, mul_one_div]
    rw [hfactor]
    have hgeom := geom_tail_bound (p := (p : ℝ)) hp_ge N
    have : Real.log (p : ℝ) * (∑ k ∈ Finset.Ico 2 (N + 1), ((1 / (p : ℝ)) ^ k))
         ≤ Real.log (p : ℝ) * (2 / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hgeom hlog_nn
    refine this.trans ?_
    rw [mul_div_assoc']
    ring_nf
    rfl
  -- Step 7: bound by ∑_n 2 log n / n^2 (Icc 2 N).
  -- This is the same set, so equality holds.
  -- Step 8: bound by ∑' n, 2 log n / n^2 = B'.
  have hstep8 :
      (∑ p ∈ Finset.Icc 2 N, (2 * Real.log (p : ℝ) / ((p : ℝ) ^ 2)))
        ≤ B' := by
    -- ∑_{p ∈ Icc 2 N} 2 log p / p^2 ≤ ∑'_n 2 log n / n^2.
    have hsum_eq :
        (∑ p ∈ Finset.Icc 2 N, (2 * Real.log (p : ℝ) / ((p : ℝ) ^ 2)))
          = ∑ p ∈ Finset.Icc 2 N, (2 * (Real.log (p : ℝ) / ((p : ℝ) ^ 2))) := by
      refine Finset.sum_congr rfl ?_
      intro p _; ring
    rw [hsum_eq, ← Finset.mul_sum]
    -- ∑_{p ∈ Icc 2 N} log p / p^2 ≤ ∑' p, log p / p^2.
    have hsumlim :
        (∑ p ∈ Finset.Icc 2 N, (Real.log (p : ℝ) / ((p : ℝ) ^ 2)))
          ≤ ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
      exact summable_log_div_sq.sum_le_tsum (Finset.Icc 2 N) (fun n _ => by
        by_cases hn : n = 0
        · subst hn; simp
        · have : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
          have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
          positivity)
    -- Multiply by 2.
    show 2 * (∑ p ∈ Finset.Icc 2 N, Real.log (p : ℝ) / ((p : ℝ) ^ 2)) ≤ B'
    unfold B'
    exact mul_le_mul_of_nonneg_left hsumlim (by norm_num)
  -- Assemble.
  calc ∑ n ∈ F, (Λ n / (n : ℝ))
      = ∑ n ∈ F, (Real.log (n.minFac : ℝ) / (n : ℝ)) := hstep1
    _ = ∑ pk ∈ F.image φ, (Real.log (pk.1 : ℝ) / ((pk.1 : ℝ) ^ pk.2)) := hstep2
    _ ≤ ∑ pk ∈ (Finset.Icc 2 N) ×ˢ (Finset.Ico 2 (N + 1)),
          (Real.log (pk.1 : ℝ) / ((pk.1 : ℝ) ^ pk.2)) := hstep4
    _ = ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Ico 2 (N + 1),
          (Real.log (p : ℝ) / ((p : ℝ) ^ k)) := hstep5
    _ ≤ ∑ p ∈ Finset.Icc 2 N, (2 * Real.log (p : ℝ) / ((p : ℝ) ^ 2)) := hstep6
    _ ≤ B' := hstep8

end PathCPrimePowerTail
end Gdbh
