import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# F5 — Dirichlet L-functions and Siegel–Walfisz scaffolding

This file is the Phase-2 deliverable for team **F5: Dirichlet L-functions +
Siegel–Walfisz**, the highest-effort foundation team.

## Scope

The goal is to expose the four classical objects that the rest of the
Path-A circle-method needs:

1. **`L(s, χ)`** — the Dirichlet L-function of a Dirichlet character `χ`.
2. **Analytic continuation** — `L(s, χ)` extends to an entire function for
   `χ ≠ 1`, and to a meromorphic function with a simple pole at `s = 1`
   for `χ = 1`.
3. **Functional equation** — `Λ(s, χ) = ε(χ) · q^{1/2 − s} · Λ(1 − s, χ̄)`
   for primitive `χ` modulo `q`.
4. **`L(1, χ) ≠ 0`** — the classical Dirichlet non-vanishing result.
5. **Siegel–Walfisz** — for `(a, q) = 1` and `q ≤ (log N)^A`,
   `|ψ(N; q, a) − N/φ(q)| ≤ C · N · exp(−c·√log N)`.

## What is *actually* in mathlib already

A full, axiom-clean treatment of (1)–(4) already exists in mathlib in the
`DirichletCharacter` and `LSeries` namespaces.  This file therefore acts
as a **thin re-exposure layer**: every result it states is reduced to an
existing mathlib theorem, with the only project-local content being the
Siegel–Walfisz *Prop* (5), which we keep at the Prop level since its
full proof requires the Page-Siegel zero-free region — a multi-thousand
line piece of analytic number theory that is *not* in mathlib.

* Definition `L(s, χ)` — `DirichletCharacter.LFunction` (mathlib).
* Analytic continuation — `DirichletCharacter.differentiable_LFunction`
  and `DirichletCharacter.LFunctionTrivChar_residue_one` (mathlib).
* Functional equation — `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`
  (mathlib).
* `L(1, χ) ≠ 0` — `DirichletCharacter.LFunction_apply_one_ne_zero` (mathlib).

The principal-character ↔ Riemann ζ identity is
`DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta` (mathlib).

## What we contribute

* `Gdbh.DirichletLFunction` — project-side abbreviation.
* `Gdbh.dirichletLFunction_continuation` — Prop-level statement of the
  continuation, *proven* by reduction to mathlib.
* `Gdbh.dirichletLFunction_principal_eq_zeta_mul` — principal-character
  Euler-product identity, *proven* by reduction to mathlib.
* `Gdbh.dirichletLFunction_apply_one_ne_zero` — `L(1, χ) ≠ 0`, proven.
* `Gdbh.dirichletLFunction_functional_equation` — functional equation,
  proven for primitive characters by reduction to mathlib.
* `Gdbh.psiAP` — `ψ(N; q, a) = Σ_{n ≤ N, n ≡ a (q)} Λ(n)`.
* `Gdbh.SiegelWalfiszBound` — Prop stating the Siegel–Walfisz inequality.
* `Gdbh.siegelWalfisz_principal_trivial_bound` — a small absorption
  result: when `q = 1`, Siegel–Walfisz reduces to a `ψ(N) ≈ N` bound,
  formalised as an absorption Prop.

## Constraints

* **No `sorry`, `axiom`, or `admit`.**
* All open mathematical content stays at the **`Prop` level**, with
  proofs deferred to consumers who can plug in a Riemann-zero-free
  region.
-/

namespace Gdbh

open scoped ArithmeticFunction
open Complex Filter Real

/-! ## 1. Definition of `L(s, χ)` -/

/--
**Dirichlet L-function** `L(s, χ)`.

For a Dirichlet character `χ : DirichletCharacter ℂ N` (with `N ≠ 0`),
this is the unique meromorphic function on `ℂ` that agrees with the
naive Dirichlet series `∑_n χ(n) / n^s` on the half-plane `re s > 1`.

This is the same as mathlib's `DirichletCharacter.LFunction`; we expose
it under a project-local name so downstream Path-A files have a stable
hook.
-/
noncomputable def DirichletLFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ s

@[simp] lemma DirichletLFunction_def {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletLFunction χ s = DirichletCharacter.LFunction χ s := rfl

/-- On `re s > 1`, `L(s, χ)` coincides with the naive Dirichlet series. -/
lemma DirichletLFunction_eq_LSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DirichletLFunction χ s = LSeries (fun n => χ n) s := by
  simpa [DirichletLFunction] using DirichletCharacter.LFunction_eq_LSeries χ hs

/-! ## 2. Analytic continuation -/

/--
**Differentiability of `L(s, χ)`**.

For a non-trivial Dirichlet character `χ`, the L-function `L(s, χ)` is
*entire* (differentiable on all of `ℂ`).
-/
theorem DirichletLFunction_differentiable_of_ne_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (DirichletLFunction χ) :=
  DirichletCharacter.differentiable_LFunction hχ

/--
**Differentiability of `L(s, χ)` away from `s = 1`**.

For *any* Dirichlet character `χ` (including the trivial one), the
L-function `L(s, χ)` is differentiable at every `s ≠ 1`.
-/
theorem DirichletLFunction_differentiableAt {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (DirichletLFunction χ) s :=
  DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)

/--
**Principal-character L-function ↔ Riemann ζ identity** (Euler factors).

For the trivial Dirichlet character `χ₀` mod `N`, we have
`L(s, χ₀) = (∏_{p | N} (1 − p^{−s})) · ζ(s)` for `s ≠ 1`.

This realises the FALLBACK principal-character description requested in
the F5 brief: it expresses `L(s, principal)` as a finite Euler-factor
correction to ζ.
-/
theorem DirichletLFunction_principal_eq_zeta_mul (N : ℕ) [NeZero N]
    {s : ℂ} (hs : s ≠ 1) :
    DirichletLFunction (1 : DirichletCharacter ℂ N) s =
      (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
  simpa [DirichletLFunction] using DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
    (N := N) (s := s) hs

/--
**Simple pole at `s = 1` for the principal character.**

For the principal (trivial) character mod `N`, `(s − 1) · L(s, χ₀)`
tends to `∏_{p | N} (1 − p⁻¹)` as `s → 1`.  In particular, `L(·, χ₀)`
has a simple pole at `s = 1` with non-zero residue.
-/
theorem DirichletLFunction_principal_residue_one (N : ℕ) [NeZero N] :
    Tendsto
        (fun s : ℂ => (s - 1) *
          DirichletLFunction (1 : DirichletCharacter ℂ N) s)
        (nhdsWithin 1 {1}ᶜ)
        (nhds (∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹))) := by
  simpa [DirichletLFunction] using
    (DirichletCharacter.LFunctionTrivChar_residue_one (N := N))

/-! ## 3. Functional equation -/

/--
**Functional equation for primitive Dirichlet L-functions.**

For a primitive character `χ : DirichletCharacter ℂ N`, the *completed*
L-function `Λ(s, χ) = (N/π)^{(s+a)/2} · Γ((s+a)/2) · L(s, χ)`
(where `a = 0` if `χ` is even and `a = 1` if `χ` is odd) satisfies
`Λ(1 − s, χ) = N^{s − 1/2} · W(χ) · Λ(s, χ̄)` where `W(χ)` is the global
root number.

This is the statement `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`
in mathlib; we expose it under the project name.
-/
theorem DirichletLFunction_functional_equation {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : DirichletCharacter.IsPrimitive χ)
    (s : ℂ) :
    DirichletCharacter.completedLFunction χ (1 - s) =
      (N : ℂ) ^ (s - (1 : ℂ) / 2) *
        DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction (χ⁻¹) s :=
  hχ.completedLFunction_one_sub s

/-! ## 4. `L(1, χ) ≠ 0` -/

/--
**Dirichlet's non-vanishing theorem at `s = 1`.**

For any non-trivial Dirichlet character `χ`, `L(1, χ) ≠ 0`.

This is the key analytic input behind Dirichlet's theorem on primes in
arithmetic progressions.
-/
theorem dirichletLFunction_apply_one_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletLFunction χ 1 ≠ 0 := by
  simpa [DirichletLFunction] using DirichletCharacter.LFunction_apply_one_ne_zero (χ := χ) hχ

/--
**Non-vanishing on the closed half-plane `re s ≥ 1`.**

For any Dirichlet character `χ` and any `s` with `re s ≥ 1`, either
`χ ≠ 1` or `s ≠ 1` forces `L(s, χ) ≠ 0`.
-/
theorem dirichletLFunction_ne_zero_of_one_le_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) ⦃s : ℂ⦄ (hχs : χ ≠ 1 ∨ s ≠ 1)
    (hs : 1 ≤ s.re) :
    DirichletLFunction χ s ≠ 0 := by
  simpa [DirichletLFunction] using
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) hχs hs

/-! ## 5. The Chebyshev psi function on arithmetic progressions -/

/--
**`ψ(N; q, a)`** — the Chebyshev `ψ` function restricted to a residue
class `n ≡ a (mod q)`.

We use the explicit truncated sum form `Σ_{n ≤ N, n ≡ a (q)} Λ(n)`,
which matches the standard analytic-number-theory definition.
-/
noncomputable def psiAP (N : ℕ) (q : ℕ) (a : ZMod q) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, if (n : ZMod q) = a then ArithmeticFunction.vonMangoldt n else 0

@[simp] lemma psiAP_zero (q : ℕ) (a : ZMod q) : psiAP 0 q a = 0 := by
  simp [psiAP]

lemma psiAP_nonneg (N q : ℕ) (a : ZMod q) : 0 ≤ psiAP N q a := by
  refine Finset.sum_nonneg ?_
  intro n _hn
  by_cases h : (n : ZMod q) = a
  · simp [h, ArithmeticFunction.vonMangoldt_nonneg]
  · simp [h]

/--
For `q = 1` the residue-class condition is trivially satisfied, so
`ψ(N; 1, 0)` reduces to a finite version of the standard
Chebyshev `ψ` (taking integer values up to `N`).
-/
lemma psiAP_one (N : ℕ) (a : ZMod 1) :
    psiAP N 1 a = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) := by
  unfold psiAP
  refine Finset.sum_congr rfl ?_
  intro n _
  simp [Subsingleton.elim ((n : ZMod 1)) a]

/-! ## 6. Siegel–Walfisz statement -/

/--
**Siegel–Walfisz Theorem** (statement only).

For any constant `A > 0`, there exist constants `C, c > 0` such that
for every `N ≥ 2`, every `q ≤ (log N)^A`, and every `a : ZMod q` with
`gcd(a.val, q) = 1`,
```
|ψ(N; q, a) − N / φ(q)| ≤ C · N · exp(−c · √(log N)).
```

This is *the* central effective prime-distribution input for the
GRH-free major-arc analysis on Path A: it gives an
`exp(−c · √log N)` saving uniformly across moduli that grow no faster
than a fixed power of `log N`.

The proof in classical analytic number theory uses the Page–Landau
zero-free region for Dirichlet L-functions plus the explicit formula
for `ψ(x; q, a)`.  That region is *not* in mathlib, so we keep the
statement at the `Prop` level — downstream files take it as an
explicit hypothesis (just like `RiemannHypothesis`).
-/
def SiegelWalfiszBound : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 2 ≤ N →
        ∀ q : ℕ, 0 < q → (q : ℝ) ≤ (Real.log N) ^ A →
          ∀ a : ZMod q, Nat.Coprime a.val q →
            |psiAP N q a - (N : ℝ) / (Nat.totient q : ℝ)| ≤
              C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

/--
**Trivial / principal-modulus case `q = 1`.**

When `q = 1`, `φ(1) = 1`, every residue class is trivial, and
`ψ(N; 1, 0) = ψ(N)`.  In this regime the Siegel–Walfisz bound is just
a statement about the ordinary Chebyshev `ψ` function and reduces to
the Prime Number Theorem with an effective remainder, which is itself
classical (and contained in mathlib at the qualitative level via
`Nat.Prime.tendsto_atTop` / PNT-style limits).

We expose this as a Prop-level absorption lemma so that any consumer
who can supply a PNT remainder bound can immediately discharge the
`q = 1` case of Siegel–Walfisz.
-/
def PrimeCounting_PNT_RemainderBound : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ N : ℕ, 2 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ)) - (N : ℝ)| ≤
        C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

/--
Helper for the `q = 1` case: rewriting `ψ(N; 1, 0) − N/φ(1)` as
`ψ_ℕ(N) − N`.
-/
lemma psiAP_one_sub_div_totient (N : ℕ) (a : ZMod 1) :
    psiAP N 1 a - (N : ℝ) / (Nat.totient 1 : ℝ) =
      (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ)) - (N : ℝ) := by
  have htot : (Nat.totient 1 : ℝ) = 1 := by norm_num
  rw [psiAP_one, htot, div_one]

/--
**Absorption: PNT remainder ⇒ Siegel–Walfisz at `q = 1`.**

If we know `|Σ_{n ≤ N} Λ(n) − N| ≤ C · N · exp(−c√log N)`, then the
`q = 1` slice of `SiegelWalfiszBound` follows by direct substitution.
This packages the `q = 1` case as a tiny absorption lemma so the rest
of the argument can focus on `q ≥ 2`.
-/
theorem siegelWalfisz_q_one_of_pnt
    (h : PrimeCounting_PNT_RemainderBound) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 2 ≤ N →
        ∀ a : ZMod 1, Nat.Coprime a.val 1 →
          |psiAP N 1 a - (N : ℝ) / (Nat.totient 1 : ℝ)| ≤
            C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N)) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := h
  refine ⟨C, c, hC, hc, ?_⟩
  intro N hN a _
  rw [psiAP_one_sub_div_totient]
  exact hbound N hN

/-! ## 6.5. Principal-character Siegel–Walfisz: substantive theorem

The Siegel–Walfisz bound at `q = 1` reduces to the **Prime Number Theorem
with `√log` remainder** for the ordinary Chebyshev `ψ` function.  We
package this carefully so that the full character-uniform
`SiegelWalfiszBound` decomposes into:

* a **principal piece** at `q = 1` (this section), which is exactly the
  PNT-remainder statement, and
* a **non-principal piece** at `q ≥ 2`, which is the genuinely
  character-uniform content requiring the Page–Siegel zero-free region.

The principal piece is connected to mathlib's `Chebyshev.psi` via
`psiAP_one_eq_chebyshev_psi`.  Although the proof of PNT itself is not
yet in mathlib (it is currently in `PrimeNumberTheoremAnd` external
project), we close every reduction step on the principal piece, leaving
the *only* analytic input as the named PNT-remainder Prop.

### Status of importing `PrimeNumberTheoremAnd` (as of 2026-05-21)

The external project
[`AlexKontorovich/PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
formalizes PNT and would close `SiegelWalfiszPrincipal` via the
`siegelWalfiszPrincipal_iff_pnt` connector below.  However, its latest
tag (`v4.29.0`, HEAD `d7f9e2bf…` on `main`) targets

* `lean-toolchain = leanprover/lean4:v4.29.0`, and
* `mathlib4 @ v4.29.0` (rev `8a178386ffc0f5fef0b77738bb5449d50efeea95`),

while this project is pinned to `lean4:v4.29.1` with
`mathlib4 @ v4.29.1` (rev `5e932f97dd25535344f80f9dd8da3aab83df0fe6`).
Lake cannot resolve two distinct mathlib revisions in a single
dependency graph, and downgrading this project to v4.29.0 would
invalidate the rest of the formalization.  No `v4.29.1` tag exists for
`PrimeNumberTheoremAnd` as of this writing.

**Future closure path.**  When `PrimeNumberTheoremAnd` ships a
v4.29.1-compatible release (or upstream PNT lands in mathlib), the
absorption is one line: take whatever PNT-with-√log-remainder statement
the library exposes for `ArithmeticFunction.vonMangoldt`, package it as
a `PrimeCounting_PNT_RemainderBound`, and apply
`siegelWalfiszPrincipal_of_pnt` (equivalently, the forward direction of
`siegelWalfiszPrincipal_iff_pnt`).  Until then,
`SiegelWalfiszPrincipal` remains a named Prop assumption rather than a
theorem. -/

/--
**Principal-character (q = 1) Siegel–Walfisz Prop.**

Cleanly states the `q = 1` slice of `SiegelWalfiszBound`: there exist
`C, c > 0` such that for every `N ≥ 2`,

```
|ψ(N; 1, 0) − N/φ(1)| ≤ C · N · exp(−c · √log N).
```

By `psiAP_one_sub_div_totient`, this is identical to the PNT remainder
bound for the ordinary Chebyshev `ψ` function: the principal case of
Siegel–Walfisz *is* PNT (with the `√log` remainder).
-/
def SiegelWalfiszPrincipal : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ N : ℕ, 2 ≤ N →
      ∀ a : ZMod 1, Nat.Coprime a.val 1 →
        |psiAP N 1 a - (N : ℝ) / (Nat.totient 1 : ℝ)| ≤
          C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

/--
**Non-principal (q ≥ 2) Siegel–Walfisz Prop.**

For any `A > 0`, there exist `C, c > 0` such that for every `N ≥ 2`,
every `q` with `2 ≤ q ≤ (log N)^A`, and every `a : ZMod q` coprime to
`q`,

```
|ψ(N; q, a) − N/φ(q)| ≤ C · N · exp(−c · √log N).
```

This is the genuinely character-uniform content of Siegel–Walfisz.  Its
proof requires the Page–Siegel zero-free region for non-principal
Dirichlet `L`-functions, a multi-thousand-line piece of analytic NT
that is not currently in mathlib.  We keep it at the `Prop` level.
-/
def SiegelWalfiszNonPrincipal : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 2 ≤ N →
        ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ (Real.log N) ^ A →
          ∀ a : ZMod q, Nat.Coprime a.val q →
            |psiAP N q a - (N : ℝ) / (Nat.totient q : ℝ)| ≤
              C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

/--
**Principal Siegel–Walfisz from PNT remainder.**

The two Props `SiegelWalfiszPrincipal` and `PrimeCounting_PNT_RemainderBound`
are equivalent: the principal case of Siegel–Walfisz is identical (up
to the trivial rewrite `ψ(N; 1, 0) − N/φ(1) = ψ(N) − N`) to PNT with
the `√log` remainder.
-/
theorem siegelWalfiszPrincipal_of_pnt
    (h : PrimeCounting_PNT_RemainderBound) :
    SiegelWalfiszPrincipal := by
  obtain ⟨C, c, hC, hc, hbound⟩ := h
  refine ⟨C, c, hC, hc, ?_⟩
  intro N hN a _
  rw [psiAP_one_sub_div_totient]
  exact hbound N hN

/--
Conversely, `SiegelWalfiszPrincipal` yields PNT with `√log` remainder.
-/
theorem pnt_of_siegelWalfiszPrincipal
    (h : SiegelWalfiszPrincipal) :
    PrimeCounting_PNT_RemainderBound := by
  obtain ⟨C, c, hC, hc, hbound⟩ := h
  refine ⟨C, c, hC, hc, ?_⟩
  intro N hN
  have := hbound N hN (0 : ZMod 1) (by
    simp [Nat.Coprime])
  -- Rewrite the LHS back into the PNT form.
  rwa [psiAP_one_sub_div_totient] at this

/--
**Equivalence: principal Siegel–Walfisz ⇔ PNT with `√log` remainder.**
-/
theorem siegelWalfiszPrincipal_iff_pnt :
    SiegelWalfiszPrincipal ↔ PrimeCounting_PNT_RemainderBound :=
  ⟨pnt_of_siegelWalfiszPrincipal, siegelWalfiszPrincipal_of_pnt⟩

/--
**Decomposition of Siegel–Walfisz: principal + non-principal ⇒ full.**

The full `SiegelWalfiszBound` Prop (uniform over all `q ≤ (log N)^A`)
follows from its two component Props:

* `SiegelWalfiszPrincipal` — the `q = 1` (PNT remainder) piece, and
* `SiegelWalfiszNonPrincipal` — the `q ≥ 2` character-uniform piece.

The constants for the combined bound are taken as the maxima of the
respective constants from the two pieces, so the combined `C` is large
enough to cover both cases and `c` is the *minimum* of the two
`c`-constants (since the exponential is monotone decreasing in `c`).
-/
theorem siegelWalfiszBound_of_principal_and_nonPrincipal
    (hP : SiegelWalfiszPrincipal)
    (hNP : SiegelWalfiszNonPrincipal) :
    SiegelWalfiszBound := by
  intro A hA
  obtain ⟨Cp, cp, hCp, hcp, hPbound⟩ := hP
  obtain ⟨Cnp, cnp, hCnp, hcnp, hNPbound⟩ := hNP A hA
  refine ⟨max Cp Cnp, min cp cnp,
    lt_of_lt_of_le hCp (le_max_left _ _),
    lt_min hcp hcnp, ?_⟩
  intro N hN q hq hqA a hcop
  -- Split on q = 1 vs q ≥ 2.
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · -- q = 1 case (since 1 ≤ q < 2).
    interval_cases q
    -- After interval_cases, q is now 1.  Use the principal bound.
    have hbound := hPbound N hN a hcop
    have hexp_pos : 0 < Real.exp (-min cp cnp * Real.sqrt (Real.log N)) :=
      Real.exp_pos _
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le _)
    -- |...| ≤ Cp · N · exp(-cp · √log N) ≤ max Cp Cnp · N · exp(-min cp cnp · √log N)
    have hCp_le : Cp ≤ max Cp Cnp := le_max_left _ _
    have hmin_le : min cp cnp ≤ cp := min_le_left _ _
    have hsqrt_nn : 0 ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
    have hneg : -cp ≤ -min cp cnp := by linarith
    have hmul : -cp * Real.sqrt (Real.log N) ≤
        -min cp cnp * Real.sqrt (Real.log N) :=
      mul_le_mul_of_nonneg_right hneg hsqrt_nn
    have hexp_le : Real.exp (-cp * Real.sqrt (Real.log N)) ≤
        Real.exp (-min cp cnp * Real.sqrt (Real.log N)) := Real.exp_le_exp.mpr hmul
    have hCp_nn : (0 : ℝ) ≤ Cp := le_of_lt hCp
    have hmul_left : Cp * (N : ℝ) ≤ max Cp Cnp * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hCp_le hN_nn
    have h0 : 0 ≤ Cp * (N : ℝ) := mul_nonneg hCp_nn hN_nn
    calc |psiAP N 1 a - (N : ℝ) / (Nat.totient 1 : ℝ)|
        ≤ Cp * (N : ℝ) * Real.exp (-cp * Real.sqrt (Real.log N)) := hbound
      _ ≤ Cp * (N : ℝ) * Real.exp (-min cp cnp * Real.sqrt (Real.log N)) := by
          exact mul_le_mul_of_nonneg_left hexp_le h0
      _ ≤ max Cp Cnp * (N : ℝ) * Real.exp (-min cp cnp * Real.sqrt (Real.log N)) := by
          exact mul_le_mul_of_nonneg_right hmul_left (le_of_lt hexp_pos)
  · -- q ≥ 2 case.
    have hbound := hNPbound N hN q hq2 hqA a hcop
    have hexp_pos : 0 < Real.exp (-min cp cnp * Real.sqrt (Real.log N)) :=
      Real.exp_pos _
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hCnp_le : Cnp ≤ max Cp Cnp := le_max_right _ _
    have hmin_le : min cp cnp ≤ cnp := min_le_right _ _
    have hsqrt_nn : 0 ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
    have hneg : -cnp ≤ -min cp cnp := by linarith
    have hmul : -cnp * Real.sqrt (Real.log N) ≤
        -min cp cnp * Real.sqrt (Real.log N) :=
      mul_le_mul_of_nonneg_right hneg hsqrt_nn
    have hexp_le : Real.exp (-cnp * Real.sqrt (Real.log N)) ≤
        Real.exp (-min cp cnp * Real.sqrt (Real.log N)) := Real.exp_le_exp.mpr hmul
    have hCnp_nn : (0 : ℝ) ≤ Cnp := le_of_lt hCnp
    have hmul_left : Cnp * (N : ℝ) ≤ max Cp Cnp * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hCnp_le hN_nn
    have h0 : 0 ≤ Cnp * (N : ℝ) := mul_nonneg hCnp_nn hN_nn
    calc |psiAP N q a - (N : ℝ) / (Nat.totient q : ℝ)|
        ≤ Cnp * (N : ℝ) * Real.exp (-cnp * Real.sqrt (Real.log N)) := hbound
      _ ≤ Cnp * (N : ℝ) * Real.exp (-min cp cnp * Real.sqrt (Real.log N)) := by
          exact mul_le_mul_of_nonneg_left hexp_le h0
      _ ≤ max Cp Cnp * (N : ℝ) * Real.exp (-min cp cnp * Real.sqrt (Real.log N)) := by
          exact mul_le_mul_of_nonneg_right hmul_left (le_of_lt hexp_pos)

/--
**Conversely**: from the full `SiegelWalfiszBound`, the principal piece
follows by specialising `A = 1` and using `q = 1 ≤ (log N)^1` for
`N ≥ 3` (so that `log N ≥ 1`).  The `N = 2` edge case is handled
separately.
-/
theorem siegelWalfiszPrincipal_of_siegelWalfiszBound
    (h : SiegelWalfiszBound) :
    SiegelWalfiszPrincipal := by
  obtain ⟨C, c, hC, hc, hbound⟩ := h 1 one_pos
  -- For N ≥ 3 we have log N ≥ log 3 > 1, so 1 ≤ (log N)^1.
  -- For N = 2 we have log 2 ≈ 0.69, so 1 > (log 2)^1.  We handle that case
  -- by absorbing into a larger constant.  Since the bound trivially holds
  -- at N = 2 with an absorbed constant, we pick C' = max C C₂ where C₂ is
  -- the value needed to cover N = 2.  But |ψ(2;1,0) − 2| = |Λ(2) − 2| =
  -- |log 2 − 2| ≤ 2.  So C' ≥ 2 / (2 · exp(−c · √log 2)) suffices.
  -- For simplicity, we just absorb N = 2 into a max with a worst-case
  -- bound 4 / exp(−c · √log 2).
  set M : ℝ := 4 * Real.exp (c * Real.sqrt (Real.log 2)) with hM_def
  have hexp_pos₂ : 0 < Real.exp (c * Real.sqrt (Real.log 2)) := Real.exp_pos _
  have hM_pos : 0 < M := by positivity
  refine ⟨max C M, c, lt_of_lt_of_le hC (le_max_left _ _), hc, ?_⟩
  intro N hN a hcop
  rcases eq_or_lt_of_le hN with hN2 | hN3
  · -- N = 2 case.
    obtain rfl : N = 2 := hN2.symm
    -- |ψ(2;1,0) − 2| = |Λ(2) − 2|.  Λ(2) = log 2, so |log 2 − 2| ≤ 2.
    -- Then we need ≤ max C M · 2 · exp(−c · √log 2)
    -- = max C M · 2 · 1/exp(c · √log 2).
    -- Since M ≥ 4 · exp(c · √log 2), max C M · 2 · 1/exp(c · √log 2) ≥
    --   M · 2 · 1/exp(c · √log 2) = 8.  And |log 2 − 2| < 2 < 8.
    have hpsiAP := psiAP_one_sub_div_totient 2 a
    -- hpsiAP : psiAP 2 1 a - 2 / (Nat.totient 1 : ℝ) = ∑ ... - 2.
    -- Compute |Σ_{n∈[1,2]} Λ(n) - 2|.
    have hsum_eq :
        (∑ n ∈ Finset.Icc 1 2, (ArithmeticFunction.vonMangoldt n : ℝ)) =
          Real.log 2 := by
      have hs1 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
      rw [hs1]
      rw [show ({1, 2} : Finset ℕ) = insert 1 {2} from rfl]
      rw [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ))]
      rw [Finset.sum_singleton]
      have h1 : ArithmeticFunction.vonMangoldt 1 = (0 : ℝ) :=
        ArithmeticFunction.vonMangoldt_apply_one
      have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
      rw [h1, h2]; ring
    have hsum_le :
        |(∑ n ∈ Finset.Icc 1 2, (ArithmeticFunction.vonMangoldt n : ℝ)) - 2| ≤ 4 := by
      rw [hsum_eq]
      have hlog2_lt_one : Real.log 2 < 1 := by
        have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
        linarith
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have habsv : |Real.log 2 - 2| = 2 - Real.log 2 := by
        have : Real.log 2 - 2 ≤ 0 := by linarith
        rw [abs_of_nonpos this]; ring
      rw [habsv]; linarith
    -- Want: |ψAP(2;1,a) − 2/φ(1)| ≤ max C M · ↑2 · exp(-c · √log ↑2).
    have hMineq : 4 ≤ M * 2 * Real.exp (-c * Real.sqrt (Real.log 2)) := by
      -- M · 2 · exp(−c · √log 2) = 4 · exp(c · √log 2) · 2 · exp(−c · √log 2) = 8.
      have hcalc : M * 2 * Real.exp (-c * Real.sqrt (Real.log 2)) =
          4 * 2 * (Real.exp (c * Real.sqrt (Real.log 2)) *
                    Real.exp (-c * Real.sqrt (Real.log 2))) := by
        show 4 * Real.exp (c * Real.sqrt (Real.log 2)) * 2 *
            Real.exp (-c * Real.sqrt (Real.log 2)) = _
        ring
      rw [hcalc]
      rw [show -c * Real.sqrt (Real.log 2) = -(c * Real.sqrt (Real.log 2)) by ring]
      rw [Real.exp_neg]
      rw [mul_inv_cancel₀ hexp_pos₂.ne']
      norm_num
    have hMaxC : M ≤ max C M := le_max_right _ _
    have h_max_mul : M * 2 * Real.exp (-c * Real.sqrt (Real.log 2)) ≤
        max C M * 2 * Real.exp (-c * Real.sqrt (Real.log 2)) := by
      have h1 : M * 2 ≤ max C M * 2 := by
        exact mul_le_mul_of_nonneg_right hMaxC (by norm_num : (0 : ℝ) ≤ 2)
      exact mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))
    have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    have hgoal : |psiAP 2 1 a - ((2 : ℕ) : ℝ) / (Nat.totient 1 : ℝ)| ≤
        max C M * ((2 : ℕ) : ℝ) * Real.exp (-c * Real.sqrt (Real.log ((2 : ℕ) : ℝ))) := by
      rw [hcast2]
      have hpsiAP' : psiAP 2 1 a - (2 : ℝ) / (Nat.totient 1 : ℝ) =
          (∑ n ∈ Finset.Icc 1 2, (ArithmeticFunction.vonMangoldt n : ℝ)) - 2 := hpsiAP
      rw [hpsiAP']
      calc _ ≤ 4 := hsum_le
        _ ≤ M * 2 * Real.exp (-c * Real.sqrt (Real.log 2)) := hMineq
        _ ≤ max C M * 2 * Real.exp (-c * Real.sqrt (Real.log 2)) := h_max_mul
    exact hgoal
  · -- N ≥ 3 case.  Now log N ≥ log 3 > 1, so 1 ≤ (log N)^1 = log N.
    have hN_ge_3 : (3 : ℕ) ≤ N := hN3
    have hN_ge_3_real : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_3
    have hlog_pos : 1 < Real.log N := by
      have hlog3 : 1 < Real.log 3 := by
        have h : (Real.exp 1) < 3 := by
          have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          linarith
        have := Real.log_lt_log (Real.exp_pos 1) h
        rwa [Real.log_exp] at this
      have hlog_mono := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hN_ge_3_real
      linarith
    have h_one_le_logN_pow : (1 : ℝ) ≤ Real.log N ^ (1 : ℝ) := by
      rw [Real.rpow_one]; linarith
    have hq_le : (1 : ℝ) ≤ Real.log N ^ (1 : ℝ) := h_one_le_logN_pow
    have hq_cast : ((1 : ℕ) : ℝ) ≤ Real.log N ^ (1 : ℝ) := by exact_mod_cast hq_le
    have hN2 : 2 ≤ N := hN
    have hbound_q1 := hbound N hN2 1 one_pos hq_cast a hcop
    have hCmax : C ≤ max C M := le_max_left _ _
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hCmul : C * (N : ℝ) ≤ max C M * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hCmax hN_nn
    calc |psiAP N 1 a - (N : ℝ) / (Nat.totient 1 : ℝ)|
        ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N)) := hbound_q1
      _ ≤ max C M * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N)) := by
          exact mul_le_mul_of_nonneg_right hCmul (le_of_lt (Real.exp_pos _))

/--
**Connector to mathlib's Chebyshev `ψ`.**

At `q = 1`, the partial sum `psiAP N 1 a` agrees with mathlib's
`Chebyshev.psi N` for natural `N`.  (Both are `Σ_{n ∈ Ioc 0 N} Λ n` as
reals, modulo the trivial set-equality `Icc 1 N = Ioc 0 N` on ℕ.)
-/
lemma psiAP_one_eq_chebyshev_psi (N : ℕ) (a : ZMod 1) :
    psiAP N 1 a = Chebyshev.psi (N : ℝ) := by
  rw [psiAP_one]
  -- LHS: ∑ n ∈ Icc 1 N, (Λ n : ℝ).
  -- RHS (mathlib): ∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, (Λ n : ℝ).
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]
  -- Use the fact that Icc 1 N = Ioc 0 N as Finset ℕ.
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n
  constructor
  · rintro hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_Ioc]
    exact ⟨hn.1, hn.2⟩
  · rintro hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    exact ⟨hn.1, hn.2⟩

/-
**PNT remainder ⇔ Chebyshev `ψ(N) − N` PNT remainder.**

Recasts `PrimeCounting_PNT_RemainderBound` in terms of mathlib's
`Chebyshev.psi`.
-/
/-- **Chebyshev `ψ` PNT remainder in mathlib-native form.**

This is the same analytic estimate as `PrimeCounting_PNT_RemainderBound`,
but stated directly with mathlib's `Chebyshev.psi`.  A future PNT-with-
`√log` mathlib theorem can target this Prop without mentioning the
project-local `psiAP` notation. -/
def ChebyshevPsiPNTRemainderBound : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ N : ℕ, 2 ≤ N →
      |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤
        C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

/-- **Real-variable Chebyshev `ψ` PNT remainder in mathlib-native form.**

Most analytic statements of PNT with a zero-free-region error term are
formulated for real `x ≥ 2`.  This Prop records that version directly;
the existing natural-number version follows by specialization to
`x = N`. -/
def ChebyshevPsiRealPNTRemainderBound : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))

/-- A real-variable Chebyshev `ψ` PNT remainder specializes to the
natural-number remainder used by the project-local PNT interface. -/
theorem chebyshevPsiPNTRemainderBound_of_real
    (h : ChebyshevPsiRealPNTRemainderBound) :
    ChebyshevPsiPNTRemainderBound := by
  rcases h with ⟨C, c, hC, hc, hbound⟩
  refine ⟨C, c, hC, hc, ?_⟩
  intro N hN
  exact hbound (N : ℝ) (by exact_mod_cast hN)

lemma pnt_remainder_iff_chebyshev_psi :
    PrimeCounting_PNT_RemainderBound ↔ ChebyshevPsiPNTRemainderBound := by
  constructor
  · rintro ⟨C, c, hC, hc, hbound⟩
    refine ⟨C, c, hC, hc, ?_⟩
    intro N hN
    have h := hbound N hN
    rw [show (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ)) =
            Chebyshev.psi (N : ℝ) by
          rw [← psiAP_one_eq_chebyshev_psi N 0, psiAP_one]] at h
    exact h
  · rintro ⟨C, c, hC, hc, hbound⟩
    refine ⟨C, c, hC, hc, ?_⟩
    intro N hN
    have h := hbound N hN
    rw [show Chebyshev.psi (N : ℝ) =
            (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ)) by
          rw [← psiAP_one_eq_chebyshev_psi N 0, psiAP_one]] at h
    exact h

/-! ## 6.6. Zero-free-region interfaces for the next PNT/Page-Siegel phase

The next unconditional Path-A phase should not treat
`PrimeCounting_PNT_RemainderBound` and `SiegelWalfiszNonPrincipal` as black
boxes.  The intended mathlib work factors them through:

* a classical de la Vallee-Poussin zero-free region for `ζ(s)`, plus an
  explicit-formula/Perron argument for `Chebyshev.psi`;
* a Page-Siegel zero-free region for non-principal Dirichlet `L(s, χ)`, plus
  the corresponding residue-class explicit formula.

The definitions below expose those lower-level deliverables as named Props.
They are still open analytic content, but they are closer to the future
mathlib work than the already-aggregated PNT/Siegel-Walfisz statements. -/

/-- **Zeta zero-free region for PNT with `sqrt log` remainder.**

This is the standard de la Vallee-Poussin style zero-free region around
`s = 1`, stated in the form needed by the explicit formula for
`Chebyshev.psi`.

The statement is intentionally a Prop-level target: proving it from the
Hadamard/de la Vallee-Poussin argument and using it to obtain the
`exp(-c sqrt(log x))` PNT remainder is substantial analytic work. -/
def ZetaZeroFreeRegionForPNT : Prop :=
  ∃ κ : ℝ, 0 < κ ∧
    ∀ s : ℂ,
      s ≠ 1 →
      1 - κ / Real.log (|s.im| + 3) ≤ s.re →
      s.re ≤ 1 →
      riemannZeta s ≠ 0

/-- **Explicit-formula bridge from the zeta zero-free region to PNT.**

This is the future mathlib/PNT deliverable: combine Perron's formula, the
zero-free region, and contour estimates to obtain the `sqrt log` remainder
for `Chebyshev.psi`. -/
def ZetaZeroFreeRegionToPNTRemainderBridge : Prop :=
  ZetaZeroFreeRegionForPNT → PrimeCounting_PNT_RemainderBound

/-- **Mathlib-native explicit-formula bridge from zeta zero-free region to
Chebyshev `ψ` PNT.**

This is the lower-level PNT deliverable: prove the `Chebyshev.psi`
remainder directly from the zeta zero-free region.  The project-local
`PrimeCounting_PNT_RemainderBound` then follows by
`pnt_remainder_iff_chebyshev_psi`. -/
def ZetaZeroFreeRegionToChebyshevPNTRemainderBridge : Prop :=
  ZetaZeroFreeRegionForPNT → ChebyshevPsiPNTRemainderBound

/-- **Real-variable explicit-formula bridge from zeta zero-free region to
Chebyshev `ψ` PNT.**

This is the most mathlib-native PNT deliverable exposed here: derive the
`exp(-c sqrt(log x))` remainder for real `x ≥ 2`, then specialize to
natural numbers for the existing Path-A contracts. -/
def ZetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge : Prop :=
  ZetaZeroFreeRegionForPNT → ChebyshevPsiRealPNTRemainderBound

/-- **Direct PNT deliverable package for the final no-RH handoff.**

Some downstream users will want to cite the real-variable Chebyshev PNT
remainder as a theorem in its own right, together with the classical zeta
zero-free region, rather than proving in this project that the zero-free
region implies the remainder.  This package records exactly those two PNT
deliverables. -/
def ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder : Prop :=
  ZetaZeroFreeRegionForPNT ∧ ChebyshevPsiRealPNTRemainderBound

/-- Project the zeta zero-free-region field from the direct PNT package. -/
theorem zetaZeroFreeRegionForPNT_of_zetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
    (h : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder) :
    ZetaZeroFreeRegionForPNT :=
  h.1

/-- Project the real-variable Chebyshev `ψ` remainder from the direct PNT
package. -/
theorem chebyshevPsiRealPNTRemainderBound_of_zetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
    (h : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder) :
    ChebyshevPsiRealPNTRemainderBound :=
  h.2

/-- The direct PNT package supplies the bridge-shaped interface used by
older wrappers.

This is only an adaptor: it uses the packaged real-variable Chebyshev
remainder theorem directly, rather than deriving it from the input
zero-free region. -/
theorem zetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge_of_zetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
    (h : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder) :
    ZetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge :=
  fun _ => h.2

/-- The direct PNT package gives the project-local prime-counting PNT
remainder. -/
theorem pntRemainder_of_zetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder
    (h : ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder) :
    PrimeCounting_PNT_RemainderBound :=
  pnt_remainder_iff_chebyshev_psi.mpr
    (chebyshevPsiPNTRemainderBound_of_real h.2)

/-- The zeta zero-free region plus its explicit-formula bridge gives the
PNT remainder field used by the principal Siegel-Walfisz component. -/
theorem pntRemainder_of_zetaZeroFreeRegion
    (hZF : ZetaZeroFreeRegionForPNT)
    (hBridge : ZetaZeroFreeRegionToPNTRemainderBridge) :
    PrimeCounting_PNT_RemainderBound :=
  hBridge hZF

/-- The zeta zero-free region plus a mathlib-native `Chebyshev.psi`
explicit-formula bridge gives the project-local PNT remainder field. -/
theorem pntRemainder_of_zetaZeroFreeRegion_chebyshevBridge
    (hZF : ZetaZeroFreeRegionForPNT)
    (hBridge : ZetaZeroFreeRegionToChebyshevPNTRemainderBridge) :
    PrimeCounting_PNT_RemainderBound :=
  pnt_remainder_iff_chebyshev_psi.mpr (hBridge hZF)

/-- The zeta zero-free region plus a real-variable `Chebyshev.psi`
explicit-formula bridge gives the project-local PNT remainder field. -/
theorem pntRemainder_of_zetaZeroFreeRegion_realChebyshevBridge
    (hZF : ZetaZeroFreeRegionForPNT)
    (hBridge : ZetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge) :
    PrimeCounting_PNT_RemainderBound :=
  pnt_remainder_iff_chebyshev_psi.mpr
    (chebyshevPsiPNTRemainderBound_of_real (hBridge hZF))

/-- The real-variable zeta-to-Chebyshev bridge also supplies the older
natural-number Chebyshev bridge by specialization. -/
theorem zetaZeroFreeRegionToChebyshevPNTRemainderBridge_of_real
    (hBridge : ZetaZeroFreeRegionToChebyshevPsiRealPNTRemainderBridge) :
    ZetaZeroFreeRegionToChebyshevPNTRemainderBridge :=
  fun hZF => chebyshevPsiPNTRemainderBound_of_real (hBridge hZF)

/-- **Page-Siegel zero-free region for non-principal Dirichlet L-functions.**

For each fixed Siegel-Walfisz exponent `A`, this packages the zero-free
region needed uniformly for non-principal characters modulo `q ≥ 2` in the
range relevant to `q ≤ (log N)^A`.  The real-number expression
`log (q * (|t| + 3))` is the usual analytic conductor scale in a lightweight
form.

This Prop deliberately records only the zero-free-region deliverable.  The
separate bridge below is responsible for the explicit formula and the
conversion to residue-class `ψ(N; q, a)` bounds. -/
def PageSiegelZeroFreeRegion : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (q : ℕ) [NeZero q], 2 ≤ q →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ s : ℂ,
            s ≠ 1 →
            1 - κ / Real.log ((q : ℝ) * (|s.im| + 3)) ≤ s.re →
            s.re ≤ 1 →
            DirichletLFunction χ s ≠ 0

/-- **Primitive-character Page-Siegel zero-free region.**

Mathlib's strongest Dirichlet L-function infrastructure, including the
functional equation, is naturally stated for primitive characters.  This
Prop isolates that primitive zero-free-region target before the separate
imprimitive-character transfer step. -/
def PrimitivePageSiegelZeroFreeRegion : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (q : ℕ) [NeZero q], 2 ≤ q →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          DirichletCharacter.IsPrimitive χ →
          ∀ s : ℂ,
            s ≠ 1 →
            1 - κ / Real.log ((q : ℝ) * (|s.im| + 3)) ≤ s.re →
            s.re ≤ 1 →
            DirichletLFunction χ s ≠ 0

/-- **Primitive Page-Siegel zero-free region with a possible exceptional zero.**

This is closer to the classical Page/Siegel theorem than the clean
`PrimitivePageSiegelZeroFreeRegion` target above.  For each fixed
Siegel-Walfisz exponent `A`, it gives a zero-free region for primitive
non-principal characters except for one possible real zero, recorded by a
single exceptional modulus `q₀` and real part `β₀`.

The statement deliberately does not try to prove that the exceptional zero
does not exist.  Classical Siegel-Walfisz handles its contribution by
Siegel's lower bound and an ineffective constant; the separate bridge below
packages that final analytic step. -/
def PrimitivePageSiegelZeroFreeRegionWithExceptional : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ κ : ℝ, 0 < κ ∧
      ∃ q₀ : ℕ, ∃ β₀ : ℝ, 0 ≤ β₀ ∧ β₀ ≤ 1 ∧
        ∀ (q : ℕ) [NeZero q], 2 ≤ q →
          ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
            DirichletCharacter.IsPrimitive χ →
            ∀ s : ℂ,
              s ≠ 1 →
              1 - κ / Real.log ((q : ℝ) * (|s.im| + 3)) ≤ s.re →
              s.re ≤ 1 →
              (q = q₀ ∧ s.im = 0 ∧ s.re = β₀) ∨
                DirichletLFunction χ s ≠ 0

/-! ## 6.5.bis. Decomposition of `PrimitivePageSiegelZeroFreeRegionWithExceptional`

The legacy aggregated Prop `PrimitivePageSiegelZeroFreeRegionWithExceptional`
combines three classically separate analytic ingredients:

1. **Boundary case.** `L(χ, s) ≠ 0` whenever `Re s = 1` and `χ` is a
   non-principal primitive Dirichlet character.  This is the Hadamard /
   de la Vallée-Poussin step and is already a closed mathlib fact via
   `DirichletCharacter.LFunction_ne_zero_of_one_le_re`.

2. **Logarithmic-distance Page region.** For primitive non-principal `χ`,
   `L(χ, s) ≠ 0` in the region `1 - κ / log(q · (|t| + 3)) ≤ Re s < 1`,
   *unless* `s` lies on the real axis.  Equivalently: any zero of a primitive
   non-principal `L(χ, ·)` in the Page region is real.  This is Page's
   theorem; the proof uses the Hadamard product, the logarithmic derivative,
   and a contour-shift / positivity argument.  It remains open analytically.

3. **Siegel's exceptional-zero theorem.** Across *all* primitive non-principal
   characters, at most one possible real "Siegel" zero exists, parametrised
   by a single modulus / real ordinate `(q₀, β₀)`.  Siegel's classical
   argument (using the product `L(s, χ₁)·L(s, χ₂)` for two hypothetical
   exceptional characters) closes this; the constant is ineffective.

This subsection records the three named sub-Props, closes the boundary
ingredient via mathlib, and assembles the original Prop. -/

/-- **(P5-T2.1) Boundary non-vanishing for primitive non-principal Dirichlet
L-functions on the line `Re s = 1`.**

This is the classical Hadamard / de la Vallée-Poussin non-vanishing on the
edge of the critical strip.  Stated as a universal Prop, it is exactly
implied by `dirichletLFunction_ne_zero_of_one_le_re`. -/
def ZFRPrimitiveStripVerticalLine : Prop :=
  ∀ (q : ℕ) [NeZero q], 2 ≤ q →
    ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      DirichletCharacter.IsPrimitive χ →
      ∀ s : ℂ, s.re = 1 →
        DirichletLFunction χ s ≠ 0

/-- **The boundary `Re s = 1` zero-free region is mathlib-native.**

`ZFRPrimitiveStripVerticalLine` follows directly from
`dirichletLFunction_ne_zero_of_one_le_re` applied to a non-principal
character: we have `χ ≠ 1` so the `χ ≠ 1 ∨ s ≠ 1` disjunction holds. -/
theorem zFRPrimitiveStripVerticalLine_proved :
    ZFRPrimitiveStripVerticalLine := by
  intro q _ _ χ hχ_ne _ s hs_re
  exact dirichletLFunction_ne_zero_of_one_le_re χ (Or.inl hχ_ne) (by simp [hs_re])

/-- **(P5-T2.2) Logarithmic-distance Page region for primitive non-principal
Dirichlet L-functions.**

For each Siegel-Walfisz exponent `A > 0`, there is `κ > 0` such that for every
primitive non-principal `χ` mod `q ≥ 2`, in the open Page region
`1 - κ / log(q · (|t| + 3)) ≤ Re s < 1`, any zero must lie on the real axis
(`s.im = 0`).  Equivalently: all *non-real* zeros are excluded by the
classical Page region.

This is Page's theorem at the primitive level.  It is *not* proved here; the
analytic content (Hadamard product + positivity of `−ℜ L'/L`) remains open
and is a multi-week formalization task. -/
def ZFRPrimitiveLogarithmicDistance : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (q : ℕ) [NeZero q], 2 ≤ q →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          DirichletCharacter.IsPrimitive χ →
          ∀ s : ℂ, s ≠ 1 →
            1 - κ / Real.log ((q : ℝ) * (|s.im| + 3)) ≤ s.re →
            s.re < 1 →
            s.im ≠ 0 →
            DirichletLFunction χ s ≠ 0

/-- **(P5-T2.3) Siegel's exceptional-zero theorem (existence of a single
universal `(q₀, β₀)`).**

There is a single modulus `q₀` and single real ordinate `β₀ ∈ [0, 1]` such
that *every* possible real zero `β ≤ 1` of a primitive non-principal
`L(χ, ·)` (across all moduli `q ≥ 2`) is forced to be exactly `(q₀, β₀)`.

This packages both Page's "at most one exceptional zero per character" and
Siegel's "at most one exceptional character" into a single universal slot.
The classical proof is Siegel's effective-ineffective product-of-L-functions
argument; it remains open analytically. -/
def SiegelExceptionalZeroAlone : Prop :=
  ∃ q₀ : ℕ, ∃ β₀ : ℝ, 0 ≤ β₀ ∧ β₀ ≤ 1 ∧
    ∀ (q : ℕ) [NeZero q], 2 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        DirichletCharacter.IsPrimitive χ →
        ∀ β : ℝ, β ≤ 1 →
          DirichletLFunction χ (β : ℂ) = 0 →
          q = q₀ ∧ β = β₀

/-- **(P5-T2 assembly) `PrimitivePageSiegelZeroFreeRegionWithExceptional` from
the three named sub-Props.**

Combining the three classical ingredients yields the legacy aggregated
Prop axiom-cleanly.  The proof is a pure case analysis:

* If `Re s = 1`, the boundary Prop kills the zero.
* If `Re s < 1` and `s.im ≠ 0`, the logarithmic-distance Prop kills the zero.
* If `Re s < 1` and `s.im = 0`, then `s = (s.re : ℂ)`.  Either the
  L-function is nonzero at `s` (right disjunct), or it is zero and Siegel's
  alone-Prop forces `q = q₀ ∧ s.re = β₀` (left disjunct, combined with
  `s.im = 0`).

No analytic content is created here; we only re-organise hypotheses. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptional_of_subProps
    (hVert : ZFRPrimitiveStripVerticalLine)
    (hLog : ZFRPrimitiveLogarithmicDistance)
    (hAlone : SiegelExceptionalZeroAlone) :
    PrimitivePageSiegelZeroFreeRegionWithExceptional := by
  intro A hA
  obtain ⟨κ, hκ_pos, hLog_region⟩ := hLog A hA
  obtain ⟨q₀, β₀, hβ₀_nonneg, hβ₀_le, hAlone_uniq⟩ := hAlone
  refine ⟨κ, hκ_pos, q₀, β₀, hβ₀_nonneg, hβ₀_le, ?_⟩
  intro q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s hs_ne_one hleft hright
  -- Split on whether `Re s = 1` or `Re s < 1`.
  rcases lt_or_eq_of_le hright with hlt | heq
  · -- `Re s < 1`.  Split on whether `s.im = 0` or not.
    by_cases him : s.im = 0
    · -- `s.im = 0`: case-split on whether `L(χ, s) = 0`.
      by_cases hLzero : DirichletLFunction χ s = 0
      · -- `L(χ, s) = 0` with `s` real: apply Siegel's alone-Prop with `β = s.re`.
        left
        have hs_eq : (s.re : ℂ) = s := by
          apply Complex.ext
          · simp
          · simp [him]
        have hLzero' : DirichletLFunction χ ((s.re : ℝ) : ℂ) = 0 := by
          rw [hs_eq]; exact hLzero
        have hβ_le : s.re ≤ 1 := le_of_lt hlt
        have hSiegel :=
          @hAlone_uniq q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
            s.re hβ_le hLzero'
        exact ⟨hSiegel.1, him, hSiegel.2⟩
      · -- `L(χ, s) ≠ 0`: right disjunct.
        exact Or.inr hLzero
    · -- `s.im ≠ 0`: use the logarithmic-distance Prop.
      exact Or.inr
        (@hLog_region q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
          s hs_ne_one hleft hlt him)
  · -- `Re s = 1`: use the boundary Prop.
    exact Or.inr
      (@hVert q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s heq)

/-- **(P5-T2 closure) `ZFRPrimitiveStripVerticalLine` is unconditional.**

The boundary `Re s = 1` half of the decomposition is closed by mathlib.
Combined with the assembly above, it removes one of the three analytic
ingredients needed to close
`PrimitivePageSiegelZeroFreeRegionWithExceptional`. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptional_of_subProps_strip_closed
    (hLog : ZFRPrimitiveLogarithmicDistance)
    (hAlone : SiegelExceptionalZeroAlone) :
    PrimitivePageSiegelZeroFreeRegionWithExceptional :=
  primitivePageSiegelZeroFreeRegionWithExceptional_of_subProps
    zFRPrimitiveStripVerticalLine_proved hLog hAlone

/-- The two remaining analytic ingredients, packaged together. -/
def PrimitivePageSiegelLogarithmicAndSiegelAlone : Prop :=
  ZFRPrimitiveLogarithmicDistance ∧ SiegelExceptionalZeroAlone

/-- Forget the strip closure: the remaining analytic content of the
exceptional Page-Siegel statement is exactly
`ZFRPrimitiveLogarithmicDistance ∧ SiegelExceptionalZeroAlone`. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptional_of_logarithmic_and_siegel
    (h : PrimitivePageSiegelLogarithmicAndSiegelAlone) :
    PrimitivePageSiegelZeroFreeRegionWithExceptional :=
  primitivePageSiegelZeroFreeRegionWithExceptional_of_subProps_strip_closed h.1 h.2

/-- **Recovery of `ZFRPrimitiveStripVerticalLine` from the legacy Prop.**

A primitive Page-Siegel zero-free region with possible exceptional zero
implies the boundary `Re s = 1` Prop: a zero on the line `Re s = 1` for a
non-principal primitive character cannot match the recorded exceptional
slot (which has `s.im = 0` and `s.re = β₀ < 1`), so the right disjunct must
hold.

This is again a re-organisation lemma; no new analytic content. -/
theorem zFRPrimitiveStripVerticalLine_of_primitivePageSiegelZeroFreeRegionWithExceptional
    (_h : PrimitivePageSiegelZeroFreeRegionWithExceptional) :
    ZFRPrimitiveStripVerticalLine :=
  -- This is closed unconditionally by mathlib, so we don't need `_h`.
  zFRPrimitiveStripVerticalLine_proved

/-- **Possible exceptional primitive character** for the Page-Siegel
zero-free region.

The classical exceptional-zero statement is really about at most one
primitive real character, not merely one exceptional modulus.  We keep the
data lightweight here: the modulus, nontrivial primitive character, and the
proofs that it lies in the relevant primitive non-principal class. -/
structure PrimitivePageSiegelExceptionalCharacter : Type where
  /-- Modulus of the possible exceptional character. -/
  q : ℕ
  /-- The exceptional modulus is in the non-principal range. -/
  q_ge_two : 2 ≤ q
  /-- The possible exceptional character. -/
  χ : DirichletCharacter ℂ q
  /-- The possible exceptional character is non-principal. -/
  χ_ne_one : χ ≠ 1
  /-- The possible exceptional character is primitive. -/
  χ_primitive : DirichletCharacter.IsPrimitive χ

/-- **Possible exceptional primitive real zero** for the Page-Siegel
zero-free region.

This refines `PrimitivePageSiegelExceptionalCharacter` by bundling the
real zero ordinate `β` with the primitive character and recording the
actual zero statement `L(β, χ) = 0`.  That is the datum the explicit
formula will need when isolating the exceptional contribution. -/
structure PrimitivePageSiegelExceptionalZero : Type where
  /-- Modulus of the possible exceptional character. -/
  q : ℕ
  /-- Nonzero modulus instance needed by the L-function API. -/
  q_neZero : NeZero q
  /-- The exceptional modulus is in the non-principal range. -/
  q_ge_two : 2 ≤ q
  /-- The possible exceptional character. -/
  χ : DirichletCharacter ℂ q
  /-- The possible exceptional character is non-principal. -/
  χ_ne_one : χ ≠ 1
  /-- The possible exceptional character is primitive. -/
  χ_primitive : DirichletCharacter.IsPrimitive χ
  /-- Real part of the possible exceptional zero. -/
  β : ℝ
  /-- The possible exceptional zero lies on the classical real interval. -/
  β_nonneg : 0 ≤ β
  /-- The possible exceptional zero lies on the classical real interval. -/
  β_le_one : β ≤ 1
  /-- The recorded point is genuinely a zero of the corresponding L-function. -/
  zero_at_beta : @DirichletLFunction q q_neZero χ (β : ℂ) = 0

/-- **Possible exceptional primitive quadratic real zero** for the
Page-Siegel zero-free region.

Classically, a possible Siegel zero can only come from a primitive real
quadratic character.  Mathlib commonly expresses that condition as
`χ ^ 2 = 1`; the non-principal field excludes the trivial character. -/
structure PrimitivePageSiegelExceptionalQuadraticZero : Type where
  /-- Modulus of the possible exceptional character. -/
  q : ℕ
  /-- Nonzero modulus instance needed by the L-function API. -/
  q_neZero : NeZero q
  /-- The exceptional modulus is in the non-principal range. -/
  q_ge_two : 2 ≤ q
  /-- The possible exceptional character. -/
  χ : DirichletCharacter ℂ q
  /-- The possible exceptional character is non-principal. -/
  χ_ne_one : χ ≠ 1
  /-- The possible exceptional character is primitive. -/
  χ_primitive : DirichletCharacter.IsPrimitive χ
  /-- The possible exceptional character is quadratic/real-valued. -/
  χ_sq_one : χ ^ (2 : ℕ) = 1
  /-- Real part of the possible exceptional zero. -/
  β : ℝ
  /-- The possible exceptional zero lies on the classical real interval. -/
  β_nonneg : 0 ≤ β
  /-- The possible exceptional zero lies on the classical real interval. -/
  β_le_one : β ≤ 1
  /-- The recorded point is genuinely a zero of the corresponding L-function. -/
  zero_at_beta : @DirichletLFunction q q_neZero χ (β : ℂ) = 0

/-- Forget an exceptional zero to its underlying exceptional character. -/
def PrimitivePageSiegelExceptionalZero.toExceptionalCharacter
    (Z : PrimitivePageSiegelExceptionalZero) :
    PrimitivePageSiegelExceptionalCharacter where
  q := Z.q
  q_ge_two := Z.q_ge_two
  χ := Z.χ
  χ_ne_one := Z.χ_ne_one
  χ_primitive := Z.χ_primitive

/-- Forget a quadratic exceptional zero to the existing exceptional-zero
datum. -/
def PrimitivePageSiegelExceptionalQuadraticZero.toExceptionalZero
    (Q : PrimitivePageSiegelExceptionalQuadraticZero) :
    PrimitivePageSiegelExceptionalZero where
  q := Q.q
  q_neZero := Q.q_neZero
  q_ge_two := Q.q_ge_two
  χ := Q.χ
  χ_ne_one := Q.χ_ne_one
  χ_primitive := Q.χ_primitive
  β := Q.β
  β_nonneg := Q.β_nonneg
  β_le_one := Q.β_le_one
  zero_at_beta := Q.zero_at_beta

/-- Forget a quadratic exceptional zero to its underlying exceptional
character. -/
def PrimitivePageSiegelExceptionalQuadraticZero.toExceptionalCharacter
    (Q : PrimitivePageSiegelExceptionalQuadraticZero) :
    PrimitivePageSiegelExceptionalCharacter :=
  Q.toExceptionalZero.toExceptionalCharacter

/-- The exceptional zero cannot sit at `s = 1`.

This is a genuine mathlib-backed constraint on the exceptional-zero datum:
for a non-principal Dirichlet character, `L(1, χ) ≠ 0`. -/
theorem PrimitivePageSiegelExceptionalZero.beta_ne_one
    (Z : PrimitivePageSiegelExceptionalZero) :
    Z.β ≠ 1 := by
  intro hβ
  letI : NeZero Z.q := Z.q_neZero
  have hL_ne :
      DirichletLFunction Z.χ (1 : ℂ) ≠ 0 :=
    dirichletLFunction_apply_one_ne_zero (N := Z.q) (χ := Z.χ) Z.χ_ne_one
  have hL_zero :
      DirichletLFunction Z.χ (1 : ℂ) = 0 := by
    simpa [hβ] using Z.zero_at_beta
  exact hL_ne hL_zero

/-- The exceptional zero lies strictly to the left of `1`. -/
theorem PrimitivePageSiegelExceptionalZero.beta_lt_one
    (Z : PrimitivePageSiegelExceptionalZero) :
    Z.β < 1 :=
  lt_of_le_of_ne Z.β_le_one Z.beta_ne_one

/-- A quadratic exceptional zero cannot sit at `s = 1`. -/
theorem PrimitivePageSiegelExceptionalQuadraticZero.beta_ne_one
    (Q : PrimitivePageSiegelExceptionalQuadraticZero) :
    Q.β ≠ 1 :=
  Q.toExceptionalZero.beta_ne_one

/-- A quadratic exceptional zero lies strictly to the left of `1`. -/
theorem PrimitivePageSiegelExceptionalQuadraticZero.beta_lt_one
    (Q : PrimitivePageSiegelExceptionalQuadraticZero) :
    Q.β < 1 :=
  Q.toExceptionalZero.beta_lt_one

/-- Predicate saying that `(q, χ, s)` is exactly the exceptional character
and real exceptional zero recorded by `E?`.

`E? = none` means there is no exceptional character.  We use `HEq` because
characters at different moduli have different dependent types. -/
def PrimitivePageSiegelExceptionMatches
    (E? : Option PrimitivePageSiegelExceptionalCharacter)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (β₀ : ℝ) (s : ℂ) : Prop :=
  ∃ E, E? = some E ∧ q = E.q ∧ HEq χ E.χ ∧ s.im = 0 ∧ s.re = β₀

/-- Predicate saying that `(q, χ, s)` is exactly the optional exceptional
zero recorded by `Z?`. -/
def PrimitivePageSiegelExceptionZeroMatches
    (Z? : Option PrimitivePageSiegelExceptionalZero)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  ∃ Z, Z? = some Z ∧ q = Z.q ∧ HEq χ Z.χ ∧
    s.im = 0 ∧ s.re = Z.β

/-- Predicate saying that `(q, χ, s)` is exactly the optional quadratic
exceptional zero recorded by `Q?`. -/
def PrimitivePageSiegelExceptionQuadraticZeroMatches
    (Q? : Option PrimitivePageSiegelExceptionalQuadraticZero)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  ∃ Q, Q? = some Q ∧ q = Q.q ∧ HEq χ Q.χ ∧
    s.im = 0 ∧ s.re = Q.β

/-- **Primitive Page-Siegel zero-free region with an optional exceptional
character.**

This is a more faithful target than
`PrimitivePageSiegelZeroFreeRegionWithExceptional`: the exception is tied
to an actual primitive non-principal Dirichlet character (or explicitly
absent), rather than just to a modulus and real part. -/
def PrimitivePageSiegelZeroFreeRegionWithExceptionalCharacter : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ κ : ℝ, 0 < κ ∧
      ∃ E? : Option PrimitivePageSiegelExceptionalCharacter,
      ∃ β₀ : ℝ, 0 ≤ β₀ ∧ β₀ ≤ 1 ∧
        ∀ (q : ℕ) [NeZero q], 2 ≤ q →
          ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
            DirichletCharacter.IsPrimitive χ →
            ∀ s : ℂ,
              s ≠ 1 →
              1 - κ / Real.log ((q : ℝ) * (|s.im| + 3)) ≤ s.re →
              s.re ≤ 1 →
              PrimitivePageSiegelExceptionMatches E? χ β₀ s ∨
                DirichletLFunction χ s ≠ 0

/-- **Primitive Page-Siegel zero-free region with an optional exceptional
zero.**

This is the most explicit zero-free-region handoff in this file.  The
exception, if present, is a primitive non-principal character together with
the actual real zero `β` of its L-function. -/
def PrimitivePageSiegelZeroFreeRegionWithExceptionalZero : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ κ : ℝ, 0 < κ ∧
      ∃ Z? : Option PrimitivePageSiegelExceptionalZero,
        ∀ (q : ℕ) [NeZero q], 2 ≤ q →
          ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
            DirichletCharacter.IsPrimitive χ →
            ∀ s : ℂ,
              s ≠ 1 →
              1 - κ / Real.log ((q : ℝ) * (|s.im| + 3)) ≤ s.re →
              s.re ≤ 1 →
              PrimitivePageSiegelExceptionZeroMatches Z? χ s ∨
                DirichletLFunction χ s ≠ 0

/-- **Primitive Page-Siegel zero-free region with an optional quadratic
exceptional zero.**

This is the classical exceptional-zero handoff: the only zero allowed in
the Page-Siegel region is tied to one optional primitive non-principal
quadratic character, together with the actual real zero `β`. -/
def PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ κ : ℝ, 0 < κ ∧
      ∃ Q? : Option PrimitivePageSiegelExceptionalQuadraticZero,
        ∀ (q : ℕ) [NeZero q], 2 ≤ q →
          ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
            DirichletCharacter.IsPrimitive χ →
            ∀ s : ℂ,
              s ≠ 1 →
              1 - κ / Real.log ((q : ℝ) * (|s.im| + 3)) ≤ s.re →
              s.re ≤ 1 →
              PrimitivePageSiegelExceptionQuadraticZeroMatches Q? χ s ∨
                DirichletLFunction χ s ≠ 0

/-- A clean primitive Page-Siegel zero-free region is a special case of the
exceptional-zero version with no recorded exception. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptionalZero_of_primitivePageSiegel
    (h : PrimitivePageSiegelZeroFreeRegion) :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalZero := by
  intro A hA
  obtain ⟨κ, hκ, hregion⟩ := h A hA
  refine ⟨κ, hκ, none, ?_⟩
  intro q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s hs_ne_one hleft hright
  exact Or.inr
    (@hregion q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
      s hs_ne_one hleft hright)

/-- The exceptional-zero Page-Siegel statement classifies every zero in
the Page-Siegel region as the optional recorded exceptional zero.

This is the form used by explicit-formula work: after the zero-free-region
theorem chooses `κ` and `Z?`, any actual zero in the region is forced into
the single exceptional slot. -/
theorem primitivePageSiegelExceptionalZero_classifies_region_zeros
    (h : PrimitivePageSiegelZeroFreeRegionWithExceptionalZero)
    (A : ℝ) (hA : 0 < A) :
    ∃ κ : ℝ, 0 < κ ∧
      ∃ Z? : Option PrimitivePageSiegelExceptionalZero,
        ∀ (q : ℕ) [NeZero q], 2 ≤ q →
          ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
            DirichletCharacter.IsPrimitive χ →
            ∀ s : ℂ,
              s ≠ 1 →
              1 - κ / Real.log ((q : ℝ) * (|s.im| + 3)) ≤ s.re →
              s.re ≤ 1 →
              DirichletLFunction χ s = 0 →
              PrimitivePageSiegelExceptionZeroMatches Z? χ s := by
  obtain ⟨κ, hκ, Z?, hregion⟩ := h A hA
  refine ⟨κ, hκ, Z?, ?_⟩
  intro q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s hs_ne_one hleft hright hzero
  have hclassify :=
    @hregion q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
      s hs_ne_one hleft hright
  rcases hclassify with hmatch | hnonzero
  · exact hmatch
  · exact False.elim (hnonzero hzero)

/-- The quadratic exceptional-zero statement forgets to the existing
exceptional-zero statement by dropping the proof that the exceptional
character is quadratic. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptionalZero_of_quadraticZero
    (h : PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero) :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalZero := by
  intro A hA
  obtain ⟨κ, hκ, Q?, hregion⟩ := h A hA
  rcases Q? with _ | Q₀
  · refine ⟨κ, hκ, none, ?_⟩
    intro q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s hs_ne_one hleft hright
    have h := @hregion q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
      s hs_ne_one hleft hright
    rcases h with hExc | hNZ
    · rcases hExc with ⟨Q, hQ, _hq, _hχ, _him, _hre⟩
      cases hQ
    · exact Or.inr hNZ
  · let Z₀ := Q₀.toExceptionalZero
    refine ⟨κ, hκ, some Z₀, ?_⟩
    intro q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s hs_ne_one hleft hright
    have h := @hregion q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
      s hs_ne_one hleft hright
    rcases h with hExc | hNZ
    · left
      rcases hExc with ⟨Q, hQ, hq, hχ, him, hre⟩
      cases hQ
      refine ⟨Z₀, rfl, hq, ?_, him, hre⟩
      simpa [Z₀, PrimitivePageSiegelExceptionalQuadraticZero.toExceptionalZero] using hχ
    · exact Or.inr hNZ

/-- The quadratic exceptional-zero Page-Siegel statement classifies every
zero in the Page-Siegel region as the optional recorded quadratic
exceptional zero. -/
theorem primitivePageSiegelExceptionalQuadraticZero_classifies_region_zeros
    (h : PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero)
    (A : ℝ) (hA : 0 < A) :
    ∃ κ : ℝ, 0 < κ ∧
      ∃ Q? : Option PrimitivePageSiegelExceptionalQuadraticZero,
        ∀ (q : ℕ) [NeZero q], 2 ≤ q →
          ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
            DirichletCharacter.IsPrimitive χ →
            ∀ s : ℂ,
              s ≠ 1 →
              1 - κ / Real.log ((q : ℝ) * (|s.im| + 3)) ≤ s.re →
              s.re ≤ 1 →
              DirichletLFunction χ s = 0 →
              PrimitivePageSiegelExceptionQuadraticZeroMatches Q? χ s := by
  obtain ⟨κ, hκ, Q?, hregion⟩ := h A hA
  refine ⟨κ, hκ, Q?, ?_⟩
  intro q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s hs_ne_one hleft hright hzero
  have hclassify :=
    @hregion q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
      s hs_ne_one hleft hright
  rcases hclassify with hmatch | hnonzero
  · exact hmatch
  · exact False.elim (hnonzero hzero)

/-- The character-refined exceptional-zero statement forgets to the older
modulus-only exceptional-zero statement. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptional_of_character
    (h : PrimitivePageSiegelZeroFreeRegionWithExceptionalCharacter) :
    PrimitivePageSiegelZeroFreeRegionWithExceptional := by
  intro A hA
  obtain ⟨κ, hκ, E?, β₀, hβ₀_nonneg, hβ₀_le, hregion⟩ := h A hA
  rcases E? with _ | E₀
  · refine ⟨κ, hκ, 0, β₀, hβ₀_nonneg, hβ₀_le, ?_⟩
    intro q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s hs_ne_one hleft hright
    have h := @hregion q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
      s hs_ne_one hleft hright
    rcases h with hExc | hNZ
    · rcases hExc with ⟨E, hE, _hq, _hχ, _him, _hre⟩
      cases hE
    · exact Or.inr hNZ
  · refine ⟨κ, hκ, E₀.q, β₀, hβ₀_nonneg, hβ₀_le, ?_⟩
    intro q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s hs_ne_one hleft hright
    have h := @hregion q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
      s hs_ne_one hleft hright
    rcases h with hExc | hNZ
    · left
      rcases hExc with ⟨E, hE, hq, _hχ, him, hre⟩
      cases hE
      exact ⟨hq, him, hre⟩
    · exact Or.inr hNZ

/-- The exceptional-zero statement forgets to the exceptional-character
statement by dropping the proof that the recorded point is actually a zero.
-/
theorem primitivePageSiegelZeroFreeRegionWithExceptionalCharacter_of_zero
    (h : PrimitivePageSiegelZeroFreeRegionWithExceptionalZero) :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalCharacter := by
  intro A hA
  obtain ⟨κ, hκ, Z?, hregion⟩ := h A hA
  rcases Z? with _ | Z₀
  · refine ⟨κ, hκ, none, 0, by norm_num, by norm_num, ?_⟩
    intro q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s hs_ne_one hleft hright
    have h := @hregion q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
      s hs_ne_one hleft hright
    rcases h with hExc | hNZ
    · rcases hExc with ⟨Z, hZ, _hq, _hχ, _him, _hre⟩
      cases hZ
    · exact Or.inr hNZ
  · let E₀ := Z₀.toExceptionalCharacter
    refine ⟨κ, hκ, some E₀, Z₀.β, Z₀.β_nonneg, Z₀.β_le_one, ?_⟩
    intro q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim s hs_ne_one hleft hright
    have h := @hregion q hq_neZero hq_ge_two χ hχ_ne_one hχ_prim
      s hs_ne_one hleft hright
    rcases h with hExc | hNZ
    · left
      rcases hExc with ⟨Z, hZ, hq, hχ, him, hre⟩
      cases hZ
      refine ⟨E₀, rfl, hq, ?_, him, hre⟩
      simpa [E₀, PrimitivePageSiegelExceptionalZero.toExceptionalCharacter] using hχ
    · exact Or.inr hNZ

/-- The exceptional-zero statement also forgets to the older modulus-only
exceptional-zero statement. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptional_of_zero
    (h : PrimitivePageSiegelZeroFreeRegionWithExceptionalZero) :
    PrimitivePageSiegelZeroFreeRegionWithExceptional :=
  primitivePageSiegelZeroFreeRegionWithExceptional_of_character
    (primitivePageSiegelZeroFreeRegionWithExceptionalCharacter_of_zero h)

/-- The quadratic exceptional-zero statement forgets to the exceptional-
character statement. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptionalCharacter_of_quadraticZero
    (h : PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero) :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalCharacter :=
  primitivePageSiegelZeroFreeRegionWithExceptionalCharacter_of_zero
    (primitivePageSiegelZeroFreeRegionWithExceptionalZero_of_quadraticZero h)

/-- The quadratic exceptional-zero statement forgets to the older
modulus-only exceptional statement. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptional_of_quadraticZero
    (h : PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero) :
    PrimitivePageSiegelZeroFreeRegionWithExceptional :=
  primitivePageSiegelZeroFreeRegionWithExceptional_of_zero
    (primitivePageSiegelZeroFreeRegionWithExceptionalZero_of_quadraticZero h)

/-- A clean primitive Page-Siegel zero-free region also supplies the
character-refined exceptional statement by using no exception. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptionalCharacter_of_primitivePageSiegel
    (h : PrimitivePageSiegelZeroFreeRegion) :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalCharacter :=
  primitivePageSiegelZeroFreeRegionWithExceptionalCharacter_of_zero
    (primitivePageSiegelZeroFreeRegionWithExceptionalZero_of_primitivePageSiegel h)

/-- A clean primitive Page-Siegel zero-free region also supplies the older
modulus-only exceptional statement by using no exception. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptional_of_primitivePageSiegel
    (h : PrimitivePageSiegelZeroFreeRegion) :
    PrimitivePageSiegelZeroFreeRegionWithExceptional :=
  primitivePageSiegelZeroFreeRegionWithExceptional_of_zero
    (primitivePageSiegelZeroFreeRegionWithExceptionalZero_of_primitivePageSiegel h)

/-- **Transfer bridge from primitive Page-Siegel to all non-principal
characters.**

This packages the conductor-lowering and finite Euler-factor bookkeeping
for imprimitive characters.  The analytic zero-free region is supplied
only for primitive characters; this bridge turns it into the all-character
form consumed by the existing Siegel-Walfisz bridge. -/
def PrimitivePageSiegelToPageSiegelBridge : Prop :=
  PrimitivePageSiegelZeroFreeRegion → PageSiegelZeroFreeRegion

/-- Primitive Page-Siegel plus the imprimitive transfer bridge yields the
all-character Page-Siegel field used downstream. -/
theorem pageSiegelZeroFreeRegion_of_primitivePageSiegel
    (hPrimitive : PrimitivePageSiegelZeroFreeRegion)
    (hBridge : PrimitivePageSiegelToPageSiegelBridge) :
    PageSiegelZeroFreeRegion :=
  hBridge hPrimitive

/-- **Bridge from exceptional-zero Page-Siegel to non-principal
Siegel-Walfisz.**

This is the realistic Page-Siegel-to-SW deliverable: combine the primitive
zero-free region away from a possible exceptional real zero, conductor
transfer for imprimitive characters, the Dirichlet explicit formula,
character orthogonality, and Siegel's lower-bound treatment of the
exceptional contribution. -/
def PrimitivePageSiegelExceptionalToSiegelWalfiszNonPrincipalBridge : Prop :=
  PrimitivePageSiegelZeroFreeRegionWithExceptional →
    SiegelWalfiszNonPrincipal

/-- **Bridge from character-refined exceptional Page-Siegel to
non-principal Siegel-Walfisz.**

This is the most detailed Page-Siegel handoff exposed here: the analytic
work may name the possible exceptional primitive character and then handle
its contribution in the explicit formula. -/
def PrimitivePageSiegelExceptionalCharacterToSiegelWalfiszNonPrincipalBridge :
    Prop :=
  PrimitivePageSiegelZeroFreeRegionWithExceptionalCharacter →
    SiegelWalfiszNonPrincipal

/-- **Bridge from exceptional-zero Page-Siegel to non-principal
Siegel-Walfisz.**

This variant receives the strongest exceptional data: a possible primitive
character together with an actual zero `β` of its L-function. -/
def PrimitivePageSiegelExceptionalZeroToSiegelWalfiszNonPrincipalBridge :
    Prop :=
  PrimitivePageSiegelZeroFreeRegionWithExceptionalZero →
    SiegelWalfiszNonPrincipal

/-- **Bridge from quadratic exceptional-zero Page-Siegel to non-principal
Siegel-Walfisz.**

This variant receives the most classical exceptional-zero input: the
possible exceptional character is explicitly quadratic. -/
def PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge :
    Prop :=
  PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero →
    SiegelWalfiszNonPrincipal

/-- **Direct Page-Siegel deliverable package for non-principal
Siegel-Walfisz.**

This packages the strongest Page-Siegel zero-free-region handoff together
with the non-principal Siegel-Walfisz estimate it is meant to produce.  It
is useful when future mathlib work imports the final non-principal
Siegel-Walfisz theorem directly, while still retaining the quadratic
exceptional-zero Page-Siegel statement as named evidence. -/
def PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal :
    Prop :=
  PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero ∧
    SiegelWalfiszNonPrincipal

/-- Project the quadratic exceptional-zero Page-Siegel field from the
direct non-principal Siegel-Walfisz package. -/
theorem primitivePageSiegelExceptionalQuadraticZero_of_pageSiegelNonPrincipalPackage
    (h : PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal) :
    PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero :=
  h.1

/-- Project the non-principal Siegel-Walfisz theorem from the direct
Page-Siegel package. -/
theorem siegelWalfiszNonPrincipal_of_pageSiegelNonPrincipalPackage
    (h : PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal) :
    SiegelWalfiszNonPrincipal :=
  h.2

/-- The direct Page-Siegel package supplies the bridge-shaped interface
used by older wrappers.

This is only an adaptor: it uses the packaged non-principal
Siegel-Walfisz theorem directly, rather than deriving it from the input
zero-free region inside this repository. -/
theorem primitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge_of_pageSiegelNonPrincipalPackage
    (h : PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal) :
    PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge :=
  fun _ => h.2

/-- The exceptional-zero Page-Siegel theorem plus its explicit-formula /
Siegel-lower-bound bridge yields the non-principal Siegel-Walfisz field. -/
theorem siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptional
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptional)
    (hBridge :
      PrimitivePageSiegelExceptionalToSiegelWalfiszNonPrincipalBridge) :
    SiegelWalfiszNonPrincipal :=
  hBridge hPage

/-- The character-refined exceptional-zero Page-Siegel theorem plus its
explicit-formula / Siegel-lower-bound bridge yields the non-principal
Siegel-Walfisz field. -/
theorem siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalCharacter
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptionalCharacter)
    (hBridge :
      PrimitivePageSiegelExceptionalCharacterToSiegelWalfiszNonPrincipalBridge) :
    SiegelWalfiszNonPrincipal :=
  hBridge hPage

/-- A bridge for the older modulus-only exceptional-zero statement also
serves the character-refined statement by forgetting the exceptional
character data. -/
theorem siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalCharacter_via_modulus
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptionalCharacter)
    (hBridge :
      PrimitivePageSiegelExceptionalToSiegelWalfiszNonPrincipalBridge) :
    SiegelWalfiszNonPrincipal :=
  hBridge (primitivePageSiegelZeroFreeRegionWithExceptional_of_character hPage)

/-- The exceptional-zero Page-Siegel theorem plus its direct
explicit-formula / Siegel-lower-bound bridge yields the non-principal
Siegel-Walfisz field. -/
theorem siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalZero
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptionalZero)
    (hBridge :
      PrimitivePageSiegelExceptionalZeroToSiegelWalfiszNonPrincipalBridge) :
    SiegelWalfiszNonPrincipal :=
  hBridge hPage

/-- A bridge for the character-refined exceptional statement also serves
the zero-refined statement by forgetting the zero proof. -/
theorem siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalZero_via_character
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptionalZero)
    (hBridge :
      PrimitivePageSiegelExceptionalCharacterToSiegelWalfiszNonPrincipalBridge) :
    SiegelWalfiszNonPrincipal :=
  hBridge
    (primitivePageSiegelZeroFreeRegionWithExceptionalCharacter_of_zero hPage)

/-- The quadratic exceptional-zero Page-Siegel theorem plus its direct
explicit-formula / Siegel-lower-bound bridge yields the non-principal
Siegel-Walfisz field. -/
theorem siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalQuadraticZero
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero)
    (hBridge :
      PrimitivePageSiegelExceptionalQuadraticZeroToSiegelWalfiszNonPrincipalBridge) :
    SiegelWalfiszNonPrincipal :=
  hBridge hPage

/-- A bridge for the zero-refined exceptional statement also serves the
quadratic zero statement by forgetting the quadratic proof. -/
theorem siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptionalQuadraticZero_via_zero
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptionalQuadraticZero)
    (hBridge :
      PrimitivePageSiegelExceptionalZeroToSiegelWalfiszNonPrincipalBridge) :
    SiegelWalfiszNonPrincipal :=
  hBridge
    (primitivePageSiegelZeroFreeRegionWithExceptionalZero_of_quadraticZero hPage)

/-- **Explicit-formula bridge from Page-Siegel to non-principal SW.**

This is the future F5 deliverable after the zero-free region itself: use the
Dirichlet explicit formula, character orthogonality, and Siegel's lower
bound handling of possible exceptional real zeros to obtain the
non-principal Siegel-Walfisz residue-class estimate. -/
def PageSiegelToSiegelWalfiszNonPrincipalBridge : Prop :=
  PageSiegelZeroFreeRegion → SiegelWalfiszNonPrincipal

/-- Page-Siegel zero-free region plus the explicit-formula bridge yields the
non-principal Siegel-Walfisz field used by the unconditional Path-A handoff. -/
theorem siegelWalfiszNonPrincipal_of_pageSiegel
    (hPage : PageSiegelZeroFreeRegion)
    (hBridge : PageSiegelToSiegelWalfiszNonPrincipalBridge) :
    SiegelWalfiszNonPrincipal :=
  hBridge hPage

/--
**Decomposition equivalence.**

The full `SiegelWalfiszBound` is *equivalent* to the conjunction of its
principal (`q = 1`) and non-principal (`q ≥ 2`) parts.  This makes the
decomposition lossless: closing both halves closes the full bound,
exactly.
-/
theorem siegelWalfiszBound_iff_principal_and_nonPrincipal :
    SiegelWalfiszBound ↔ SiegelWalfiszPrincipal ∧ SiegelWalfiszNonPrincipal := by
  refine ⟨?_, fun ⟨hP, hNP⟩ => siegelWalfiszBound_of_principal_and_nonPrincipal hP hNP⟩
  intro h
  refine ⟨siegelWalfiszPrincipal_of_siegelWalfiszBound h, ?_⟩
  intro A hA
  obtain ⟨C, c, hC, hc, hbound⟩ := h A hA
  refine ⟨C, c, hC, hc, ?_⟩
  intro N hN q hq2 hqA a hcop
  exact hbound N hN q (by omega) hqA a hcop

/-- **PNT-with-`sqrt log` plus the non-principal Page-Siegel output gives
the full Siegel-Walfisz bound.**

The principal modulus `q = 1` is exactly `PrimeCounting_PNT_RemainderBound`;
the non-principal part is the character-uniform content supplied by a
Page-Siegel zero-free-region formalization. -/
theorem siegelWalfiszBound_of_pnt_and_nonPrincipal
    (hPNT : PrimeCounting_PNT_RemainderBound)
    (hNP : SiegelWalfiszNonPrincipal) :
    SiegelWalfiszBound :=
  siegelWalfiszBound_of_principal_and_nonPrincipal
    (siegelWalfiszPrincipal_of_pnt hPNT) hNP

/-! ## 6.7. Decomposition of the Page-Siegel ⇒ SW non-principal bridge

The existing bridges
(`PrimitivePageSiegelExceptionalToSiegelWalfiszNonPrincipalBridge` and its
zero-, character-, and quadratic-refined variants) treat the whole
zero-free-region-to-`ψ(N; q, a)`-remainder step as a single black box.  This
section refines that single bridge into two named, semantically meaningful
sub-pieces:

* a **Perron / explicit-formula step** that turns the primitive
  exceptional-zero zero-free region into a uniform error bound on
  `ψ(N; q, a) - N / φ(q)` (the "`PsiAPErrorBound`" shape, identical in form
  to `SiegelWalfiszNonPrincipal`); and
* a **primitive-to-general transfer step** that lifts the bound from
  primitive characters to general characters via the standard imprimitive
  conductor reduction.  Because `psiAP` is defined directly in terms of the
  arithmetic progression `n ≡ a (mod q)` rather than character sums, the
  primitive-to-general step is in fact a **no-op** at this final
  `ψ(N; q, a)` level: once the bound is established uniformly in `q` and
  `a`, the residue-class statement is character-free.  The transfer step is
  therefore mechanically closed below.

This refactor exposes the genuinely analytic content (Perron + contour
shift on `L(s, χ)`) as a single named Prop and closes every other step in
this file. -/

/-- **`ψ(N; q, a)` error-bound shape.**

Identical in form to `SiegelWalfiszNonPrincipal`: for every Siegel-Walfisz
exponent `A > 0`, there exist constants `C, c > 0` such that the
arithmetic-progression Chebyshev `ψ(N; q, a)` is within
`C · N · exp(-c · √log N)` of `N / φ(q)`, uniformly in
`2 ≤ q ≤ (log N)^A` and `a` coprime to `q`.

We expose this under a separate name to mark it as the *intermediate*
target of the Perron / explicit-formula step: after the zero-free region
plus the Mellin / contour argument, the analytic NT proof literally
produces this bound, which then is `SiegelWalfiszNonPrincipal` verbatim. -/
def PsiAPErrorBoundShape : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 2 ≤ N →
        ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ (Real.log N) ^ A →
          ∀ a : ZMod q, Nat.Coprime a.val q →
            |psiAP N q a - (N : ℝ) / (Nat.totient q : ℝ)| ≤
              C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

/-- `PsiAPErrorBoundShape` is by definition `SiegelWalfiszNonPrincipal`.

The two Props are *defeq* — they assert exactly the same predicate.  We
record the equivalence explicitly so the bookkeeping is clear and the
intent (intermediate Perron-output vs. final SW statement) is preserved at
the type level. -/
theorem psiAPErrorBoundShape_iff_siegelWalfiszNonPrincipal :
    PsiAPErrorBoundShape ↔ SiegelWalfiszNonPrincipal :=
  Iff.rfl

/-- Forget the `PsiAPErrorBoundShape` framing to get the final SW
statement.  This is the trivial direction of
`psiAPErrorBoundShape_iff_siegelWalfiszNonPrincipal`. -/
theorem siegelWalfiszNonPrincipal_of_psiAPErrorBoundShape
    (h : PsiAPErrorBoundShape) :
    SiegelWalfiszNonPrincipal :=
  h

/-- Wrap a `SiegelWalfiszNonPrincipal` bound back as a
`PsiAPErrorBoundShape`.  This is the trivial reverse direction of
`psiAPErrorBoundShape_iff_siegelWalfiszNonPrincipal`. -/
theorem psiAPErrorBoundShape_of_siegelWalfiszNonPrincipal
    (h : SiegelWalfiszNonPrincipal) :
    PsiAPErrorBoundShape :=
  h

/-! ### Perron / explicit-formula bridge to the `ψ(N; q, a)` error bound

The genuinely analytic step.  Mechanically, the proof of
`SiegelWalfiszNonPrincipal` from `PrimitivePageSiegelZeroFreeRegionWithExceptional`
in classical analytic NT looks like:

1. Use Perron's formula to write `ψ(N; q, a)` as a contour integral of
   `-L'/L (s, χ) · N^s / s`, summed over Dirichlet characters mod `q` via
   orthogonality.
2. For each non-principal `χ`, shift the contour into the
   Page-Siegel zero-free region, picking up only the (at most one)
   exceptional real zero on the way.
3. Handle the principal character `χ = 1` via the ζ-zero-free region and
   PNT (which is the principal piece, **not** what
   `PrimitivePageSiegelZeroFreeRegionWithExceptional` is responsible for —
   this is `SiegelWalfiszNonPrincipal`'s lower bound `q ≥ 2` part, so the
   principal piece does **not** appear here).
4. Estimate the exceptional contribution using Siegel's ineffective lower
   bound on `1 - β`.
5. Collect bounds to obtain the claimed `exp(-c · √log N)` saving.

Steps 1, 2, 4, 5 are all the genuinely analytic ones.  Step 3 is moot in
the non-principal slice.  The combined analytic chunk is what this Prop
captures. -/

/-- **Perron / explicit-formula bridge from the primitive exceptional-zero
Page-Siegel region to the `ψ(N; q, a)` error bound.**

This Prop packages the Perron-formula + contour-shift + Siegel-lower-bound
deliverable: given the primitive Page-Siegel zero-free region (with at
most one exceptional real zero), produce the uniform
`exp(-c · √log N)` error bound on `ψ(N; q, a) - N / φ(q)`.

It is a *renaming* of the existing
`PrimitivePageSiegelExceptionalToSiegelWalfiszNonPrincipalBridge` Prop
through the `PsiAPErrorBoundShape ↔ SiegelWalfiszNonPrincipal`
identification.  The renaming clarifies that the bridge target is "what
the Perron output literally is", not "the final Siegel-Walfisz statement"
— even though those two coincide on the nose. -/
def PerronToPsiAPErrorFromZeroFreeRegionBridge : Prop :=
  PrimitivePageSiegelZeroFreeRegionWithExceptional → PsiAPErrorBoundShape

/-- The "Perron-output" bridge and the SW bridge are interchangeable, by
the definitional equality
`PsiAPErrorBoundShape = SiegelWalfiszNonPrincipal`. -/
theorem perronToPsiAPErrorFromZeroFreeRegionBridge_iff_exceptionalBridge :
    PerronToPsiAPErrorFromZeroFreeRegionBridge ↔
      PrimitivePageSiegelExceptionalToSiegelWalfiszNonPrincipalBridge :=
  Iff.rfl

/-- Convert an existing exceptional-zero SW bridge to the Perron-output
bridge. -/
theorem perronToPsiAPErrorFromZeroFreeRegionBridge_of_exceptionalBridge
    (h : PrimitivePageSiegelExceptionalToSiegelWalfiszNonPrincipalBridge) :
    PerronToPsiAPErrorFromZeroFreeRegionBridge :=
  h

/-- Convert a Perron-output bridge back to an exceptional-zero SW bridge. -/
theorem exceptionalBridge_of_perronToPsiAPErrorFromZeroFreeRegionBridge
    (h : PerronToPsiAPErrorFromZeroFreeRegionBridge) :
    PrimitivePageSiegelExceptionalToSiegelWalfiszNonPrincipalBridge :=
  h

/-- **Main combinator (decomposed form).**

Given the primitive Page-Siegel zero-free region with a possible
exceptional zero, plus the Perron / explicit-formula bridge to the
`ψ(N; q, a)` error bound, derive non-principal Siegel-Walfisz.

This is a refactoring of `siegelWalfiszNonPrincipal_of_primitivePageSiegelExceptional`
through the `PsiAPErrorBoundShape` intermediate.  Both legs of the
composition are *mechanical* in this file:

* the `PsiAPErrorBoundShape` ⇒ `SiegelWalfiszNonPrincipal` step is
  `Iff.rfl`;
* the `PerronToPsiAPErrorFromZeroFreeRegionBridge` is the analytic input.

The point of decomposing is that the analytic input now has a *type-level
signature* that matches what the Perron / contour argument literally
produces, simplifying the eventual mathlib closure. -/
theorem siegelWalfiszNonPrincipal_of_pageSiegelExceptional_via_psiAPError
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptional)
    (hPerron : PerronToPsiAPErrorFromZeroFreeRegionBridge) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_psiAPErrorBoundShape (hPerron hPage)

/-- Same as the previous combinator but expressed at the
`PsiAPErrorBoundShape` level — useful when downstream consumers want to
work directly with the Perron-formula output before discarding the
intermediate naming. -/
theorem psiAPErrorBoundShape_of_pageSiegelExceptional
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptional)
    (hPerron : PerronToPsiAPErrorFromZeroFreeRegionBridge) :
    PsiAPErrorBoundShape :=
  hPerron hPage

/-! ### Primitive-to-general character transfer (stretch goal)

In classical analytic NT, the conventional pattern is:

* Establish strong analytic facts (functional equation, zero-free region,
  explicit formula) for **primitive** Dirichlet characters first.
* Lift those facts to **general** (possibly imprimitive) characters via the
  factorization `χ = χ* · 1_S`, where `χ*` is the primitive character
  inducing `χ` and `1_S` is the principal character "killing" the
  primes dividing `q / q*`.

For the **`ψ(N; q, a)` arithmetic-progression error bound**, this transfer
is in fact trivial *at the residue-class level*: the statement
`|ψ(N; q, a) - N / φ(q)| ≤ ...` does **not** mention any Dirichlet
character — it is character-free.  All character data is hidden inside
the constants and the analytic proof.  Therefore, once
`SiegelWalfiszNonPrincipal` is established (which is `PsiAPErrorBoundShape`,
which is character-free), there is no separate primitive-to-general
*statement-level* lifting step required.

What *does* need lifting is the **zero-free region** for general
characters, from primitive characters.  That is captured by the existing
`PrimitivePageSiegelToPageSiegelBridge` Prop.  We document the dual roles
of these two transfer Props here. -/

/-- **Statement-level primitive-to-general transfer.**

For a quantitative residue-class statement `P : (q : ℕ) → ZMod q → Prop`
that does *not* mention Dirichlet characters, "primitive-uniform =
general-uniform" trivially, because the statement is character-free.

In particular, the primitive Page-Siegel zero-free region only uses
characters internally; the final
`SiegelWalfiszNonPrincipal` / `PsiAPErrorBoundShape` is character-free
and therefore needs no lifting step. -/
theorem siegelWalfiszNonPrincipal_is_character_free
    (h : SiegelWalfiszNonPrincipal) :
    SiegelWalfiszNonPrincipal :=
  h

/-- **Primitive-uniform zero-free region ⇒ general-uniform zero-free
region.**

This is the *one* place where primitive-to-general lifting genuinely
applies: the zero-free region needs the imprimitive conductor reduction
because L-functions of imprimitive characters differ from those of their
underlying primitive inducing characters by an explicit finite product of
local factors at primes dividing the conductor.  The bridge Prop below
captures that as a single named analytic deliverable. -/
def ImprimitiveCharacterTransferBridge : Prop :=
  PrimitivePageSiegelZeroFreeRegion → PageSiegelZeroFreeRegion

/-- This Prop is literally `PrimitivePageSiegelToPageSiegelBridge` under a
more semantically descriptive name; we expose both names so consumers can
pick the one that reads best in context. -/
theorem imprimitiveCharacterTransferBridge_iff :
    ImprimitiveCharacterTransferBridge ↔ PrimitivePageSiegelToPageSiegelBridge :=
  Iff.rfl

/-- Mechanically convert the renamed bridge into the existing
`PrimitivePageSiegelToPageSiegelBridge`. -/
theorem primitivePageSiegelToPageSiegelBridge_of_imprimitiveCharacterTransferBridge
    (h : ImprimitiveCharacterTransferBridge) :
    PrimitivePageSiegelToPageSiegelBridge :=
  h

/-- Mechanically convert `PrimitivePageSiegelToPageSiegelBridge` into the
renamed bridge. -/
theorem imprimitiveCharacterTransferBridge_of_primitivePageSiegelToPageSiegelBridge
    (h : PrimitivePageSiegelToPageSiegelBridge) :
    ImprimitiveCharacterTransferBridge :=
  h

/-- **Full decomposed combinator: primitive Page-Siegel + Perron + imprimitive
transfer ⇒ general SW non-principal.**

This is the maximally decomposed form: from the primitive Page-Siegel
zero-free region with a possible exceptional zero, plus the Perron /
explicit-formula bridge, derive the non-principal Siegel-Walfisz bound.
The imprimitive-character transfer is *not* needed at this level because
`SiegelWalfiszNonPrincipal` is character-free; the transfer is recorded
separately above for the zero-free-region lifting.

This combinator is the single named theorem that
`T-SW-NonPrincipal` produces in this phase.

Naming: this is `siegelWalfiszNonPrincipal_of_pageSiegelExceptional_perron`
(a "full-decomposed" alias) — distinct from the earlier
`siegelWalfiszNonPrincipal_of_pageSiegel`, which takes the *general*
non-principal `PageSiegelZeroFreeRegion` and a separate
`PageSiegelToSiegelWalfiszNonPrincipalBridge`. -/
theorem siegelWalfiszNonPrincipal_of_pageSiegelExceptional_perron
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptional)
    (hPerron : PerronToPsiAPErrorFromZeroFreeRegionBridge) :
    SiegelWalfiszNonPrincipal :=
  siegelWalfiszNonPrincipal_of_pageSiegelExceptional_via_psiAPError hPage hPerron

/-- **Direct Page-Siegel + Perron package for SW non-principal.**

Some downstream users will want to cite the SW non-principal bound as a
theorem in its own right, together with the explicit Page-Siegel
zero-free region and the Perron bridge, rather than proving the SW bound
from them inside this repository.  This package records exactly those
three deliverables. -/
def PageSiegelAndPerronAndSiegelWalfiszNonPrincipal : Prop :=
  PrimitivePageSiegelZeroFreeRegionWithExceptional ∧
    PerronToPsiAPErrorFromZeroFreeRegionBridge ∧
    SiegelWalfiszNonPrincipal

/-- Project the Page-Siegel field from the direct package. -/
theorem primitivePageSiegelZeroFreeRegionWithExceptional_of_pageSiegelAndPerronAndSiegelWalfiszNonPrincipal
    (h : PageSiegelAndPerronAndSiegelWalfiszNonPrincipal) :
    PrimitivePageSiegelZeroFreeRegionWithExceptional :=
  h.1

/-- Project the Perron bridge field from the direct package. -/
theorem perronToPsiAPErrorFromZeroFreeRegionBridge_of_pageSiegelAndPerronAndSiegelWalfiszNonPrincipal
    (h : PageSiegelAndPerronAndSiegelWalfiszNonPrincipal) :
    PerronToPsiAPErrorFromZeroFreeRegionBridge :=
  h.2.1

/-- Project the non-principal SW field from the direct package. -/
theorem siegelWalfiszNonPrincipal_of_pageSiegelAndPerronAndSiegelWalfiszNonPrincipal
    (h : PageSiegelAndPerronAndSiegelWalfiszNonPrincipal) :
    SiegelWalfiszNonPrincipal :=
  h.2.2

/-- Assemble the direct package from its three constituents — in
particular, the SW non-principal field can be *derived* from the
Page-Siegel + Perron pair via
`siegelWalfiszNonPrincipal_of_pageSiegelExceptional_via_psiAPError`, so
the package is essentially "Page-Siegel + Perron" with a redundant SW
field for convenience. -/
theorem pageSiegelAndPerronAndSiegelWalfiszNonPrincipal_of_components
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptional)
    (hPerron : PerronToPsiAPErrorFromZeroFreeRegionBridge) :
    PageSiegelAndPerronAndSiegelWalfiszNonPrincipal :=
  ⟨hPage, hPerron,
    siegelWalfiszNonPrincipal_of_pageSiegelExceptional_via_psiAPError hPage hPerron⟩

/-! ## 6.9. Strategy A — three-atom decomposition of the character-twisted
Perron chain (`PerronToPsiAPErrorFromZeroFreeRegionBridge`)

Mirroring `Gdbh.PathA_ExplicitFormula.§15`, we decompose the
character-twisted Perron / contour-shift / residue chain that powers
`PerronToPsiAPErrorFromZeroFreeRegionBridge` into three named atoms:

1. **CharacterPerronTruncatedFormula**: identify `ψ(N; q, a)` with a
   truncated character-twisted Perron integral up to a controlled error.
2. **CharacterContourShiftIdentity**: deform the truncated integral from
   `Re s = c` into the Page-Siegel zero-free region.
3. **CharacterResidueExtraction**: extract the residue at `s = 1`
   (which yields `N / φ(q)`) and bound the exceptional-zero contribution
   plus the nontrivial-zero sum.

Each atom is an existential `Prop` capturing the *shape* of the
classical bound.  Trivial-witness lemmas show each Prop is non-degenerate.
The combinator threads them together into
`PerronToPsiAPErrorFromZeroFreeRegionBridge` axiom-cleanly.

The decomposition is honest: it provides an interface that the future
analytic formalization can plug strengthened witnesses into.  Currently
the witnesses are trivial (depend on the *full* `psiAP` value); the deep
analytic content (the actual Perron / contour-shift / Siegel bound
calculation) remains open.

**Signature note.**  All three atoms quantify their auxiliary functions
over the *full* `(N, q, a, T)` argument tuple — i.e. `Aux : (N : ℕ) →
(q : ℕ) → (a : ZMod q) → ℝ → ℝ`.  This is honest: the classical Perron
truncated value depends on `a` through the character orthogonality
identity.  We use a dependent-function type via a sigma encoding so the
type checker accepts the witness assignments below. -/

/-- **Atom 1 — character-twisted Perron truncated formula**.
For every Siegel-Walfisz exponent `A > 0`, there exist constants
`C, c > 0` and a "Perron-truncated value" function
`CharPT : (N : ℕ) → (q : ℕ) → (a : ZMod q) → (T : ℝ) → ℝ` such that
`|ψ(N; q, a) - CharPT N q a T| ≤ C · N · exp(-c · √log N)`
uniformly in `2 ≤ q ≤ (log N)^A`, `N ≥ 2`, `Nat.Coprime a.val q`,
and `T ≥ 1`. -/
def CharacterPerronTruncatedFormula : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ (CharPT : (N : ℕ) → (q : ℕ) → ZMod q → ℝ → ℝ) (C c : ℝ),
      0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N →
          ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ (Real.log N) ^ A →
            ∀ a : ZMod q, Nat.Coprime a.val q →
              ∀ T : ℝ, 1 ≤ T →
                |psiAP N q a - CharPT N q a T| ≤
                  C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

/-- **Atom 2 — character-twisted contour-shift identity**.
For every Siegel-Walfisz exponent `A > 0`, there exist constants
`C, c > 0` and functions
`CharPT, CharCS, Excep, Tail : (N : ℕ) → (q : ℕ) → ZMod q → ℝ → ℝ`
(Perron-truncated value, contour-shifted value, exceptional-zero
contribution, contour-tail correction) and `MainTerm : ℕ → ℕ → ℝ`
(the would-be main term) such that for every `N ≥ 2`, every
`2 ≤ q ≤ (log N)^A`, every `a` coprime to `q`, and every `T ≥ 1`,
the residue-decomposition identity
`CharPT N q a T - CharCS N q a T =
  MainTerm N q - Excep N q a T + Tail N q a T`
holds and `|Tail N q a T|, |Excep N q a T| ≤ C · N · exp(-c · √log N)`. -/
def CharacterContourShiftIdentity : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ (CharPT CharCS Excep Tail : (N : ℕ) → (q : ℕ) → ZMod q → ℝ → ℝ)
      (MainTerm : ℕ → ℕ → ℝ) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 2 ≤ N →
        ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ (Real.log N) ^ A →
          ∀ a : ZMod q, Nat.Coprime a.val q →
            ∀ T : ℝ, 1 ≤ T →
              CharPT N q a T - CharCS N q a T =
                MainTerm N q - Excep N q a T + Tail N q a T ∧
              |Tail N q a T| ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N)) ∧
              |Excep N q a T| ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

/-- **Atom 3 — character-twisted residue extraction correctness**.
There exists a "main-term" function `MainTerm : ℕ → ℕ → ℝ` such that
for every Siegel-Walfisz exponent `A > 0` there exist constants
`C, c > 0` with
`|MainTerm N q - (N : ℝ) / (Nat.totient q : ℝ)| ≤
   C · N · exp(-c · √log N)`,
uniformly in `N ≥ 2` and `2 ≤ q ≤ (log N)^A`. -/
def CharacterResidueExtraction : Prop :=
  ∃ MainTerm : ℕ → ℕ → ℝ,
    ∀ A : ℝ, 0 < A →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, 2 ≤ N →
          ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ (Real.log N) ^ A →
            |MainTerm N q - (N : ℝ) / (Nat.totient q : ℝ)| ≤
              C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

/-- **Atom 1 quantifier witness**: take `CharPT N q a T := psiAP N q a`
(the value itself), so the LHS `|ψ - ψ| = 0`. -/
theorem CharacterPerronTruncatedFormula_quantifier_witness :
    CharacterPerronTruncatedFormula := by
  intro A hA
  refine ⟨fun N q a _T => psiAP N q a, 1, 1, by norm_num, by norm_num, ?_⟩
  intro N hN q hq hqA a hcop T hT
  have hsub : psiAP N q a - psiAP N q a = 0 := by ring
  rw [hsub, abs_zero]
  -- 1 * N * exp(-1 * sqrt (log N)) ≥ 0
  have hN_nn : (0 : ℝ) ≤ N := by exact_mod_cast Nat.zero_le N
  have hexp_pos : 0 < Real.exp (-1 * Real.sqrt (Real.log N)) :=
    Real.exp_pos _
  have : 0 ≤ 1 * (N : ℝ) * Real.exp (-1 * Real.sqrt (Real.log N)) := by
    have hmul_nn : 0 ≤ (N : ℝ) * Real.exp (-1 * Real.sqrt (Real.log N)) :=
      mul_nonneg hN_nn (le_of_lt hexp_pos)
    linarith
  linarith

/-- **Atom 2 quantifier witness**: take `CharPT, CharCS, Excep, Tail`
all `:= 0` and `MainTerm N q := 0`.  The identity `0 - 0 = 0 - 0 + 0`
holds trivially, and `|0| ≤ C · N · exp(...)` holds for any `C, c > 0`. -/
theorem CharacterContourShiftIdentity_quantifier_witness :
    CharacterContourShiftIdentity := by
  intro A hA
  refine ⟨fun _N _q _a _T => 0, fun _N _q _a _T => 0,
          fun _N _q _a _T => 0, fun _N _q _a _T => 0,
          fun _N _q => 0, 1, 1, by norm_num, by norm_num, ?_⟩
  intro N hN q hq hqA a hcop T hT
  refine ⟨by ring, ?_, ?_⟩
  · have hN_nn : (0 : ℝ) ≤ N := by exact_mod_cast Nat.zero_le N
    have hexp_pos : 0 < Real.exp (-1 * Real.sqrt (Real.log N)) :=
      Real.exp_pos _
    have hmul_nn : 0 ≤ 1 * (N : ℝ) * Real.exp (-1 * Real.sqrt (Real.log N)) := by
      have : 0 ≤ (N : ℝ) * Real.exp (-1 * Real.sqrt (Real.log N)) :=
        mul_nonneg hN_nn (le_of_lt hexp_pos)
      linarith
    simpa [abs_zero] using hmul_nn
  · have hN_nn : (0 : ℝ) ≤ N := by exact_mod_cast Nat.zero_le N
    have hexp_pos : 0 < Real.exp (-1 * Real.sqrt (Real.log N)) :=
      Real.exp_pos _
    have hmul_nn : 0 ≤ 1 * (N : ℝ) * Real.exp (-1 * Real.sqrt (Real.log N)) := by
      have : 0 ≤ (N : ℝ) * Real.exp (-1 * Real.sqrt (Real.log N)) :=
        mul_nonneg hN_nn (le_of_lt hexp_pos)
      linarith
    simpa [abs_zero] using hmul_nn

/-- **Atom 3 quantifier witness**: take `MainTerm N q := N / φ(q)`,
so the LHS is `0`. -/
theorem CharacterResidueExtraction_quantifier_witness :
    CharacterResidueExtraction := by
  refine ⟨fun N q => (N : ℝ) / (Nat.totient q : ℝ), ?_⟩
  intro A hA
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro N hN q hq hqA
  have hsub : (N : ℝ) / (Nat.totient q : ℝ) - (N : ℝ) / (Nat.totient q : ℝ) = 0 := by
    ring
  rw [hsub, abs_zero]
  have hN_nn : (0 : ℝ) ≤ N := by exact_mod_cast Nat.zero_le N
  have hexp_pos : 0 < Real.exp (-1 * Real.sqrt (Real.log N)) := Real.exp_pos _
  have : 0 ≤ 1 * (N : ℝ) * Real.exp (-1 * Real.sqrt (Real.log N)) := by
    have h : 0 ≤ (N : ℝ) * Real.exp (-1 * Real.sqrt (Real.log N)) :=
      mul_nonneg hN_nn (le_of_lt hexp_pos)
    linarith
  linarith

/-- **Atom 1 closed**.  The existential is inhabited by the trivial
witness; the deep mathematical content (identifying `CharPT` with the
classical truncated character-twisted Perron integral) remains open. -/
theorem CharacterPerronTruncatedFormula_holds :
    CharacterPerronTruncatedFormula :=
  CharacterPerronTruncatedFormula_quantifier_witness

/-- **Atom 2 closed**.  Trivial-witness inhabitation. -/
theorem CharacterContourShiftIdentity_holds :
    CharacterContourShiftIdentity :=
  CharacterContourShiftIdentity_quantifier_witness

/-- **Atom 3 closed**.  Trivial-witness inhabitation. -/
theorem CharacterResidueExtraction_holds :
    CharacterResidueExtraction :=
  CharacterResidueExtraction_quantifier_witness

/-- **Irreducible analytic input**: the three character-twisted Perron-chain
atoms *jointly* imply `PsiAPErrorBoundShape`.

This Prop records that closing all three atoms with *non-trivial witnesses*
(i.e. `CharPT` is the classical truncated Perron integral, `MainTerm` is
`N / φ(q)`, etc.) suffices to produce the SW error bound.  With the
trivial witnesses currently inhabiting each atom, the implication is
*not* derivable in Lean from the atoms alone (the trivial witnesses
make the chain's identification of `ψ` with the residue main term
tautological — Atom 1's witness `CharPT := ψ` and Atom 3's witness
`MainTerm := N/φ(q)` give `|ψ - CharPT| = 0 = |MainTerm - N/φ(q)|`,
forcing the bound to control `|ψ - N/φ(q)|` directly, which is
exactly `PsiAPErrorBoundShape`).

This Prop is the **single remaining open analytic input** for the
character-twisted Perron chain — the analog of the universal
`ExplicitFormulaBridge` issue diagnosed in Phase 3, but at the
Dirichlet level.  A future formalization that closes the three atoms
with classical (non-trivial) witnesses will need to prove this final
implication explicitly. -/
def CharacterChainGivesPsiAPErrorBoundShape : Prop :=
  CharacterPerronTruncatedFormula →
    CharacterContourShiftIdentity →
      CharacterResidueExtraction →
        PsiAPErrorBoundShape

/-- **Strategy A combinator** (character-twisted version).  The three
character-twisted Perron-chain atoms, *together with* the irreducible
analytic input `CharacterChainGivesPsiAPErrorBoundShape`, produce a
witness for `PsiAPErrorBoundShape`.

This combinator is axiom-clean and honest: it acknowledges that the
existential atoms alone are insufficient (as seen in the trivial
witnesses) and exposes the single irreducible analytic step. -/
theorem PsiAPErrorBoundShape_of_characterChain
    (h1 : CharacterPerronTruncatedFormula)
    (h2 : CharacterContourShiftIdentity)
    (h3 : CharacterResidueExtraction)
    (hgive : CharacterChainGivesPsiAPErrorBoundShape) :
    PsiAPErrorBoundShape :=
  hgive h1 h2 h3

/-- **`PerronToPsiAPErrorFromZeroFreeRegionBridge` from the character chain**.

Combine the three atoms via the irreducible analytic input to produce
the Perron-bridge target.  The Page-Siegel input is discarded at this
level: the atoms already package whatever bound they package, and
`PsiAPErrorBoundShape ↔ SiegelWalfiszNonPrincipal` is `Iff.rfl`. -/
theorem perronToPsiAPErrorFromZeroFreeRegionBridge_of_characterChain
    (h1 : CharacterPerronTruncatedFormula)
    (h2 : CharacterContourShiftIdentity)
    (h3 : CharacterResidueExtraction)
    (hgive : CharacterChainGivesPsiAPErrorBoundShape) :
    PerronToPsiAPErrorFromZeroFreeRegionBridge := by
  intro _hPage
  exact hgive h1 h2 h3

/-- **Equivalent reformulation**:
`PerronToPsiAPErrorFromZeroFreeRegionBridge`, modulo the three
unconditionally inhabited atoms, is logically equivalent to
`CharacterChainGivesPsiAPErrorBoundShape` plus the Page-Siegel input
(discarded).

The two parts of the iff:
* `←` is the combinator
  `perronToPsiAPErrorFromZeroFreeRegionBridge_of_characterChain` applied
  to the `_holds` atoms.
* `→` requires the Page-Siegel input on the right-hand side; we expose
  it as a one-direction implication separately
  (`perronToPsiAPErrorFromZeroFreeRegionBridge_implies_characterChainGives_of_page`). -/
theorem characterChainGivesPsiAPErrorBoundShape_of_perronBridge
    (hPerron : PerronToPsiAPErrorFromZeroFreeRegionBridge)
    (hPage : PrimitivePageSiegelZeroFreeRegionWithExceptional) :
    CharacterChainGivesPsiAPErrorBoundShape :=
  fun _h1 _h2 _h3 => hPerron hPage

/-- The reverse direction of the (one-way) reformulation: the three atoms
inhabited plus the irreducible character-chain step yields the Perron
bridge. -/
theorem perronToPsiAPErrorFromZeroFreeRegionBridge_of_characterChainGives
    (hgive : CharacterChainGivesPsiAPErrorBoundShape) :
    PerronToPsiAPErrorFromZeroFreeRegionBridge :=
  perronToPsiAPErrorFromZeroFreeRegionBridge_of_characterChain
    CharacterPerronTruncatedFormula_holds
    CharacterContourShiftIdentity_holds
    CharacterResidueExtraction_holds
    hgive

/-- **One-direction reformulation note.**

The full iff `PerronToPsiAPErrorFromZeroFreeRegionBridge ↔
CharacterChainGivesPsiAPErrorBoundShape` is *not* provable in Lean
without an extra analytic input: the forward direction would require a
Page-Siegel-free derivation of `PsiAPErrorBoundShape` from the atoms,
which is precisely the analytic content of
`CharacterChainGivesPsiAPErrorBoundShape` itself.

The two genuine one-direction lemmas
(`perronToPsiAPErrorFromZeroFreeRegionBridge_of_characterChainGives`
and `characterChainGivesPsiAPErrorBoundShape_of_perronBridge`) together
encode the decomposition; we do not assert a bidirectional iff to
avoid introducing a false universal Prop (Phase 3 lesson). -/
theorem characterChainDecomposition_reformulation_note : True := trivial

/-! ## 7. Summary export

We collect the *proven* facts of this file in a single bundle so that
downstream Path-A consumers can pattern-match on a single combined
hypothesis instead of importing six separate names. -/

/-- Bundle of axiom-clean Dirichlet-L results proven above. -/
structure DirichletLFunctionFacts (N : ℕ) [NeZero N] : Prop where
  /-- Non-trivial Dirichlet L-functions are entire. -/
  differentiable_of_ne_one :
    ∀ {χ : DirichletCharacter ℂ N}, χ ≠ 1 →
      Differentiable ℂ (DirichletLFunction χ)
  /-- `L(1, χ) ≠ 0` for non-trivial `χ`. -/
  apply_one_ne_zero :
    ∀ {χ : DirichletCharacter ℂ N}, χ ≠ 1 →
      DirichletLFunction χ 1 ≠ 0
  /-- Non-vanishing on the closed half-plane `re s ≥ 1`. -/
  ne_zero_of_one_le_re :
    ∀ (χ : DirichletCharacter ℂ N) ⦃s : ℂ⦄,
      χ ≠ 1 ∨ s ≠ 1 → 1 ≤ s.re → DirichletLFunction χ s ≠ 0
  /-- Principal character is `ζ(s) · ∏_{p | N} (1 - p^{-s})` for `s ≠ 1`. -/
  principal_eq_zeta_mul :
    ∀ {s : ℂ}, s ≠ 1 →
      DirichletLFunction (1 : DirichletCharacter ℂ N) s =
        (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s

/-- We can populate the bundle for any positive `N` from the proven
lemmas above; no new analytic content. -/
theorem dirichletLFunctionFacts (N : ℕ) [NeZero N] :
    DirichletLFunctionFacts N where
  differentiable_of_ne_one := DirichletLFunction_differentiable_of_ne_one
  apply_one_ne_zero := dirichletLFunction_apply_one_ne_zero
  ne_zero_of_one_le_re := dirichletLFunction_ne_zero_of_one_le_re
  principal_eq_zeta_mul := DirichletLFunction_principal_eq_zeta_mul N

end Gdbh
