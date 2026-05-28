# GOAL: Binary Goldbach Conjecture — Unconditional Lean 4 Formalization

  ## Mission Statement

  Resolve the Binary Goldbach Conjecture **unconditionally** in Lean 4 / mathlib v4.29.1:

  ```
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n
  ```

  This conjecture has been **open since Christian Goldbach's 1742 letter to Euler — 283 years unsolved**. You are tasked with attempting it via maximum-parallel multi-agent attack. The goal is genuine
  breakthrough OR clear documentation of which obstructions are insurmountable, NOT fake closure.

  ## Working Environment

  - **Repo**: `/Users/tommy/Downloads/gdbh`, Lean 4 + mathlib v4.29.1
  - **Existing infrastructure (~174 axiom-clean files)**:
    - Path C K-Goldbach: K ≤ 202 closed modulo 4 named open Props
    - Path A Binary-under-RH: 17 fields closed modulo 9 named open Props
    - 15 honest false-Prop catches documented
  - **Headlines**: `Gdbh.PathCKGoldbachUnconditional.pathC_kGoldbach_unconditional`, `Gdbh.strongGoldbach_under_RH_phase5_reduced`
  - **Tools**: Agent, TeamCreate, Bash, Edit, Write, Read

  ## Hard Truths (Must Acknowledge)

  1. Binary Goldbach unconditional has resisted ~200 years of attacks by the strongest mathematicians (Hardy, Littlewood, Vinogradov, Selberg, Erdős, Tao, Helfgott, ...).
  2. Best known unconditional partial result: Ramaré 1995, every even n ≥ 4 is sum of ≤ 6 primes (K=6).
  3. Helfgott 2013 settled TERNARY Goldbach (odd n ≥ 7 = sum of 3 primes) — that effort took ~700 pages over 3 papers.
  4. RH-conditional Binary Goldbach is known (Hardy-Littlewood 1923) and is Path A's target.
  5. **Lean cannot close what humans haven't proved.** If unconditional resolution exists, it requires genuinely new mathematics.

  ## Strategy: 5 Parallel Attack Vectors

  Spawn 5 independent agent teams, each with 3-8 sub-agents. Each team picks ONE vector and runs continuous research-style attack. Reconvene every 72 hours for cross-pollination.

  ### Vector A — Analytic (Beyond-RH Zero-Free Region)
  **Hypothesis**: Establish quantitative zero-free region for L(s, χ) strong enough that the explicit formula for ψ(x, q, a) gives error o(x/log²x) uniformly over residue classes mod q ≤ x^{1/2-ε}.
  - A1: Korobov-Vinogradov zero-free region formalization
  - A2: Bombieri-Vinogradov mean-value formalization
  - A3: log-free zero density estimates
  - Success criterion: Path A's `psiBound` unconditional, hence Binary Goldbach unconditional.

  ### Vector B — Sieve (Path C K-Goldbach Refinement)
  **Hypothesis**: Push K from current ≤202 down to K=2 via iterative sieve refinement + density argument.
  - B1: Close all 4 Path C residuals → fully unconditional K ≤ 202
  - B2: Selberg Λ² with optimal weights → K ≤ 50 (Ramaré's domain)
  - B3: Density-increment argument à la Gallagher → K ≤ 10
  - B4: Cross with circle method → K ≤ 4
  - B5: Final push to K = 2 (this is where the conjecture lives)
  - Success criterion: K=2 achieved.

  ### Vector C — Schnirelmann Density Improvement
  **Hypothesis**: Improve σ(primesSumset) bound to σ ≥ 1/2 (which gives basis order 2 directly via Mann's theorem).
  - C1: Sharp Mertens-3 + singular series tail
  - C2: Mann's α+β theorem at threshold
  - C3: Tao-Vu concentration for prime pair count
  - Success criterion: σ ≥ 1/2 unconditional → Binary Goldbach.

  ### Vector D — Heath-Brown Identity
  **Hypothesis**: Use Heath-Brown's identity for Λ(n) → bilinear form decomposition → improve minor-arc Vinogradov beyond classical bounds.
  - D1: Heath-Brown identity formalization
  - D2: Type-I sum bounds with mathlib's Dirichlet series infrastructure
  - D3: Type-II bilinear sum bounds (this is the hard part)
  - D4: Bourgain-style cancellation in trilinear forms
  - Success criterion: minor-arc bound o(x/log³x) → Binary Goldbach via circle method.

  ### Vector E — Novel/AI-Discovered Approaches
  **Hypothesis**: Approaches outside standard analytic NT.
  - E1: Polynomial Method (Croot-Lev-Pach) applied to additive structure of primes
  - E2: Green-Tao density-increment for prime gaps
  - E3: Model theory of o-minimal expansions of ℝ + transfer principles
  - E4: Reverse mathematics — find subsystem where Goldbach is provable
  - E5: ML pattern recognition on prime gaps for missing inequality
  - Success criterion: ANY new partial result not in known literature.

  ## Multi-Agent Orchestration Rules

  1. **File-write isolation**: Each agent writes to its own file. No shared files.
  2. **Axiom hygiene (strict)**: Only `[Classical.choice, Quot.sound, propext]`. Zero `sorry`, `axiom`, `admit`.
  3. **`lake build` green discipline**: After every closure, verify `lake build` succeeds.
  4. **Honest catch protocol**: If you find a contradiction or known obstruction, STOP and write up as "false-Prop catch" or "obstruction note". These are valuable.
  5. **Decomposition discipline**: Decompose ambitious Props into strictly smaller named sub-Props. Track residuals.
  6. **NO `audit_lean_axioms.py`**: 30+ min stall. Use per-theorem `#print axioms` via `lake env lean --stdin`.
  7. **NO existential witness exploitation**: Don't pick trivial witnesses (k=0, C=∞) to vacuously close.
  8. **Honesty over progress**: A documented obstruction is worth more than a fake closure.
  9. **Persistent sub-agent trees allowed**: First-layer agents may spawn child or grandchild agents for score-positive subgoals. There is no mandatory close step after dispatch; keep useful child agents open for follow-up context. Close only on ownership drift, non-positive score drift, lost report path, high-score timeout without usable progress, or explicit user/controller decision.

  ## Concrete Round 1 Launch

  Spawn these 25 agents immediately, in parallel:

  | Agent | Vector | Target |
  |-------|--------|--------|
  | A1-A3 | A | Zero-free region (3 sub-agents) |
  | B1-B5 | B | K-reduction (5 sub-agents) |
  | C1-C3 | C | Schnirelmann density (3 sub-agents) |
  | D1-D4 | D | Heath-Brown / Vinogradov (4 sub-agents) |
  | E1-E5 | E | Novel approaches (5 sub-agents) |
  | M1-M5 | Meta | Cross-pollination + integration (5 sub-agents) |

  Each agent gets:
  - Specific named Prop to attack
  - File-write target
  - Maximum 48-hour reporting cycle; remain open if still carrying useful score-positive context
  - Honest-catch protocol

  ## Decomposition Templates

  For each named Prop being attacked, follow this template:
  ```
  P = <ambitious Prop>
  Sub-Props: P₁, P₂, ..., Pₖ (each strictly smaller than P)
  Bridges: ∀i, theorem Pᵢ_implies_progress : Pᵢ → (P ∨ smaller residual)
  Closure attempts: theorem Pᵢ_holds : Pᵢ (axiom-clean or expose smallest residual)
  ```

  ## Realistic Fallback Goals

  If Binary Goldbach unconditional resists (very likely outcome), produce ANY of:

  | Fallback | Difficulty | Value |
  |----------|-----------|-------|
  | F1: Close Path C fully (K ≤ 202 unconditional in Lean) | Easy | High |
  | F2: Improve to K ≤ 100 unconditional | Medium | High |
  | F3: Close Path A fully (Binary RH-conditional in Lean) | Hard | High |
  | F4: Improve Ramaré K=6 in Lean | Very Hard | Historic |
  | F5: New obstruction documented in Lean | Medium | High |
  | F6: Density-1 Goldbach in Lean | Easy | Medium |

  ## Reporting

  - **Hourly**: brief progress ping per active agent
  - **Daily**: technical summary with `lake build` status + axiom audit
  - **Weekly**: comprehensive writeup + cross-pollination synthesis
  - **Major breakthrough**: full Lean proof + paper-style mathematical writeup
  - **Obstruction discovery**: write up reasoning + future paths

  ## Bottom Line

  You are attempting one of the most famous open problems in mathematics. Do so with:
  - Maximum agent parallelism (25+ agents)
  - Maximum mathematical honesty (15+ catches already documented in Path C)
  - Maximum decomposition discipline (named sub-Props everywhere)
  - Maximum patience (multi-week-month research)

  The realistic outcome distribution:
  - 70% probability: Achieve F1-F2 (Path C close + sub-100 K)
  - 20% probability: Achieve F3-F4 (Path A close or sub-10 K)
  - 8% probability: Achieve F5 (genuine obstruction insight)
  - 2% probability: Genuine progress toward unconditional Binary Goldbach

  A 2% probability on humanity's 283-year unsolved problem is **MASSIVELY worth attempting** with sufficient compute.

  Begin Round 1 NOW. Report initial decomposition + first attack vectors within 24 hours.
