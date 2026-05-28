import Gdbh.VonMangoldtGoldbach
import Mathlib.Analysis.Fourier.ZMod

namespace Gdbh
namespace DiscreteCircleMethod

open Finset
open ZMod
open scoped BigOperators ZMod

noncomputable def zmodConvolution {N : Nat} [NeZero N]
    (f g : ZMod N → ℂ) (t : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * g (t - x)

theorem zmodDftConvolution_apply {N : Nat} [NeZero N]
    (f g : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun t => zmodConvolution f g t) k =
      ZMod.dft f k * ZMod.dft g k := by
  simp only [ZMod.dft_apply, zmodConvolution, smul_eq_mul]
  calc
    ∑ t : ZMod N, stdAddChar (-(t * k)) *
        ∑ x : ZMod N, f x * g (t - x)
        = ∑ t : ZMod N, ∑ x : ZMod N,
            stdAddChar (-(t * k)) * (f x * g (t - x)) := by
          simp [Finset.mul_sum]
    _ = ∑ x : ZMod N, ∑ t : ZMod N,
            stdAddChar (-(t * k)) * (f x * g (t - x)) := by
          rw [Finset.sum_comm]
    _ = ∑ x : ZMod N, ∑ y : ZMod N,
            stdAddChar (-((x + y) * k)) * (f x * g y) := by
          congr with x
          refine Fintype.sum_equiv (Equiv.subRight x) _ _ ?_
          intro t
          congr 1
          congr 1
          simp [Equiv.subRight]
    _ = ∑ x : ZMod N, ∑ y : ZMod N,
            (stdAddChar (-(k * x)) * f x) *
              (stdAddChar (-(k * y)) * g y) := by
          congr with x
          congr with y
          have hchar : stdAddChar (-((x + y) * k)) =
              stdAddChar (-(k * x)) * stdAddChar (-(k * y)) := by
            rw [← AddChar.map_add_eq_mul]
            congr 1
            ring_nf
          rw [hchar]
          ring
    _ = ∑ x : ZMod N,
          (stdAddChar (-(k * x)) * f x) *
            ∑ y : ZMod N, stdAddChar (-(k * y)) * g y := by
          simp [Finset.mul_sum]
    _ = (∑ x : ZMod N, stdAddChar (-(k * x)) * f x) *
          ∑ y : ZMod N, stdAddChar (-(k * y)) * g y := by
          rw [Finset.sum_mul]
    _ = (∑ x : ZMod N, stdAddChar (-(x * k)) * f x) *
          ∑ y : ZMod N, stdAddChar (-(y * k)) * g y := by
          congr 2 <;> ext z <;> ring_nf

theorem zmodConvolution_eq_inverse_dft {N : Nat} [NeZero N]
    (f g : ZMod N → ℂ) (t : ZMod N) :
    zmodConvolution f g t =
      (ZMod.dft.symm (fun k => ZMod.dft f k * ZMod.dft g k)) t := by
  have hfun :
      ZMod.dft (fun t => zmodConvolution f g t) =
        fun k => ZMod.dft f k * ZMod.dft g k := by
    ext k
    exact zmodDftConvolution_apply f g k
  calc
    zmodConvolution f g t =
        (ZMod.dft.symm
          (ZMod.dft (fun t => zmodConvolution f g t))) t := by
          simp
    _ = (ZMod.dft.symm (fun k => ZMod.dft f k * ZMod.dft g k)) t := by
          rw [hfun]

noncomputable def zmodFourierTerm {N : Nat} [NeZero N]
    (f g : ZMod N → ℂ) (t k : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ *
    (ZMod.stdAddChar (k * t) * (ZMod.dft f k * ZMod.dft g k))

theorem zmodConvolution_eq_fourier_sum {N : Nat} [NeZero N]
    (f g : ZMod N → ℂ) (t : ZMod N) :
    zmodConvolution f g t = ∑ k : ZMod N, zmodFourierTerm f g t k := by
  rw [zmodConvolution_eq_inverse_dft]
  rw [ZMod.invDFT_apply]
  simp [zmodFourierTerm, Finset.mul_sum]

noncomputable def zmodMajorArcContribution {N : Nat} [NeZero N]
    (f g : ZMod N → ℂ) (majorArcs : Finset (ZMod N))
    (t : ZMod N) : ℂ :=
  ∑ k ∈ majorArcs, zmodFourierTerm f g t k

noncomputable def zmodMinorArcContribution {N : Nat} [NeZero N]
    (f g : ZMod N → ℂ) (majorArcs : Finset (ZMod N))
    (t : ZMod N) : ℂ :=
  ∑ k ∈ (Finset.univ.filter (fun k : ZMod N => k ∉ majorArcs)),
    zmodFourierTerm f g t k

def zmodMinorFrequencies {N : Nat} [NeZero N]
    (majorArcs : Finset (ZMod N)) : Finset (ZMod N) :=
  Finset.univ.filter (fun k : ZMod N => k ∉ majorArcs)

theorem mem_zmodMinorFrequencies {N : Nat} [NeZero N]
    {majorArcs : Finset (ZMod N)} {k : ZMod N} :
    k ∈ zmodMinorFrequencies majorArcs ↔ k ∉ majorArcs := by
  simp [zmodMinorFrequencies]

theorem zmodMinorFrequencies_card_le {N : Nat} [NeZero N]
    (majorArcs : Finset (ZMod N)) :
    (zmodMinorFrequencies majorArcs).card ≤ N := by
  have hcard :
      (zmodMinorFrequencies majorArcs).card ≤
        Fintype.card (ZMod N) :=
    Finset.card_le_univ _
  simpa [ZMod.card] using hcard

theorem zmodMinorFrequencies_card_real_le {N : Nat} [NeZero N]
    (majorArcs : Finset (ZMod N)) :
    ((zmodMinorFrequencies majorArcs).card : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast zmodMinorFrequencies_card_le majorArcs

theorem zmodConvolution_eq_major_add_minor {N : Nat} [NeZero N]
    (f g : ZMod N → ℂ) (majorArcs : Finset (ZMod N))
    (t : ZMod N) :
    zmodConvolution f g t =
      zmodMajorArcContribution f g majorArcs t +
        zmodMinorArcContribution f g majorArcs t := by
  rw [zmodConvolution_eq_fourier_sum]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (ZMod N)))
    (p := fun k : ZMod N => k ∈ majorArcs)
    (f := fun k => zmodFourierTerm f g t k)
  simpa [zmodMajorArcContribution, zmodMinorArcContribution] using hsplit.symm

theorem zmodMajorArcContribution_norm_le_sum_norm {N : Nat} [NeZero N]
    (f g : ZMod N → ℂ) (majorArcs : Finset (ZMod N))
    (t : ZMod N) :
    ‖zmodMajorArcContribution f g majorArcs t‖ ≤
      ∑ k ∈ majorArcs, ‖zmodFourierTerm f g t k‖ := by
  simpa [zmodMajorArcContribution] using
    (norm_sum_le majorArcs (fun k => zmodFourierTerm f g t k))

theorem zmodMinorArcContribution_norm_le_sum_norm {N : Nat} [NeZero N]
    (f g : ZMod N → ℂ) (majorArcs : Finset (ZMod N))
    (t : ZMod N) :
    ‖zmodMinorArcContribution f g majorArcs t‖ ≤
      ∑ k ∈ zmodMinorFrequencies majorArcs,
        ‖zmodFourierTerm f g t k‖ := by
  simpa [zmodMinorArcContribution, zmodMinorFrequencies] using
    (norm_sum_le (zmodMinorFrequencies majorArcs)
      (fun k => zmodFourierTerm f g t k))

theorem zmodMinorArcContribution_norm_le_of_term_bound {N : Nat}
    [NeZero N] (f g : ZMod N → ℂ)
    (majorArcs : Finset (ZMod N)) (t : ZMod N)
    {termBound : ZMod N → ℝ}
    (hterm :
      ∀ k ∈ zmodMinorFrequencies majorArcs,
        ‖zmodFourierTerm f g t k‖ ≤ termBound k) :
    ‖zmodMinorArcContribution f g majorArcs t‖ ≤
      ∑ k ∈ zmodMinorFrequencies majorArcs, termBound k :=
  (zmodMinorArcContribution_norm_le_sum_norm f g majorArcs t).trans
    (Finset.sum_le_sum hterm)

noncomputable def vonMangoldtZModWeight (N : Nat) [NeZero N]
    (x : ZMod N) : ℂ :=
  (vonMangoldtWeight x.val : ℂ)

noncomputable def vonMangoldtZModDft
    (n : Nat) (k : ZMod n.succ) : ℂ :=
  ZMod.dft (vonMangoldtZModWeight n.succ) k

noncomputable def rawVonMangoldtDftSquareFourierTerm
    (n : Nat) (k : ZMod n.succ) : ℂ :=
  (n.succ : ℂ)⁻¹ *
    (ZMod.stdAddChar (k * (n : ZMod n.succ)) *
      (vonMangoldtZModDft n k) ^ 2)

theorem rawVonMangoldtDftSquareFourierTerm_eq_zmodFourierTerm
    (n : Nat) (k : ZMod n.succ) :
    rawVonMangoldtDftSquareFourierTerm n k =
      zmodFourierTerm
        (vonMangoldtZModWeight n.succ)
        (vonMangoldtZModWeight n.succ)
        (n : ZMod n.succ)
        k := by
  simp [rawVonMangoldtDftSquareFourierTerm, vonMangoldtZModDft,
    zmodFourierTerm, pow_two]

theorem rawVonMangoldtDftSquareFourierTerm_norm
    (n : Nat) (k : ZMod n.succ) :
    ‖rawVonMangoldtDftSquareFourierTerm n k‖ =
      ‖((n.succ : ℂ)⁻¹)‖ * ‖vonMangoldtZModDft n k‖ ^ 2 := by
  simp [rawVonMangoldtDftSquareFourierTerm, pow_two]

theorem sum_zmod_val_succ (n : Nat) (F : Nat → ℂ) :
    (∑ x : ZMod n.succ, F x.val) = (Finset.range n.succ).sum F := by
  change (∑ x : Fin n.succ, F x.val) = (Finset.range n.succ).sum F
  rw [Finset.sum_range]

theorem natCast_sub_val_succ (n : Nat) (x : ZMod n.succ) :
    (((n : ZMod n.succ) - x).val) = n - x.val := by
  have hnval : ((n : ZMod n.succ).val) = n :=
    ZMod.val_natCast_of_lt (Nat.lt_succ_self n)
  have hle : x.val ≤ ((n : ZMod n.succ).val) := by
    rw [hnval]
    exact Nat.le_of_lt_succ (ZMod.val_lt x)
  simpa [hnval] using
    (ZMod.val_sub (a := (n : ZMod n.succ)) (b := x) hle)

theorem zmodVonMangoldtConvolution_natCast_eq_raw (n : Nat) :
    zmodConvolution (vonMangoldtZModWeight n.succ)
      (vonMangoldtZModWeight n.succ) (n : ZMod n.succ) =
      (RawVonMangoldtGoldbachSum n : ℂ) := by
  rw [rawVonMangoldtGoldbachSum_eq_weight_sum]
  dsimp [zmodConvolution, vonMangoldtZModWeight]
  simp_rw [natCast_sub_val_succ]
  simp
  exact sum_zmod_val_succ n
    (fun m : Nat =>
      (vonMangoldtWeight m : ℂ) * (vonMangoldtWeight (n - m) : ℂ))

theorem rawVonMangoldtGoldbachSum_complex_eq_dft_square_sum
    (n : Nat) :
    (RawVonMangoldtGoldbachSum n : ℂ) =
      ∑ k : ZMod n.succ, rawVonMangoldtDftSquareFourierTerm n k := by
  calc
    (RawVonMangoldtGoldbachSum n : ℂ) =
        zmodConvolution
          (vonMangoldtZModWeight n.succ)
          (vonMangoldtZModWeight n.succ)
          (n : ZMod n.succ) := by
      exact (zmodVonMangoldtConvolution_natCast_eq_raw n).symm
    _ = ∑ k : ZMod n.succ,
        zmodFourierTerm
          (vonMangoldtZModWeight n.succ)
          (vonMangoldtZModWeight n.succ)
          (n : ZMod n.succ)
          k := by
      exact zmodConvolution_eq_fourier_sum
        (vonMangoldtZModWeight n.succ)
        (vonMangoldtZModWeight n.succ)
        (n : ZMod n.succ)
    _ = ∑ k : ZMod n.succ,
        rawVonMangoldtDftSquareFourierTerm n k := by
      simp [rawVonMangoldtDftSquareFourierTerm_eq_zmodFourierTerm]

theorem rawVonMangoldtGoldbachSum_complex_eq_fourier_major_add_minor
    (n : Nat) (majorArcs : Finset (ZMod n.succ)) :
    (RawVonMangoldtGoldbachSum n : ℂ) =
      zmodMajorArcContribution
        (vonMangoldtZModWeight n.succ)
        (vonMangoldtZModWeight n.succ)
        majorArcs
        (n : ZMod n.succ) +
      zmodMinorArcContribution
        (vonMangoldtZModWeight n.succ)
        (vonMangoldtZModWeight n.succ)
        majorArcs
        (n : ZMod n.succ) := by
  rw [← zmodVonMangoldtConvolution_natCast_eq_raw n]
  exact zmodConvolution_eq_major_add_minor
    (vonMangoldtZModWeight n.succ)
    (vonMangoldtZModWeight n.succ)
    majorArcs
    (n : ZMod n.succ)

noncomputable def rawVonMangoldtFourierMajorArcComplexContribution
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) : ℂ :=
  zmodMajorArcContribution
    (vonMangoldtZModWeight n.succ)
    (vonMangoldtZModWeight n.succ)
    (majorArcs n)
    (n : ZMod n.succ)

noncomputable def rawVonMangoldtFourierMinorArcComplexContribution
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) : ℂ :=
  zmodMinorArcContribution
    (vonMangoldtZModWeight n.succ)
    (vonMangoldtZModWeight n.succ)
    (majorArcs n)
    (n : ZMod n.succ)

theorem rawVonMangoldtFourierMajorArcComplexContribution_eq_dft_square_sum
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) :
    rawVonMangoldtFourierMajorArcComplexContribution majorArcs n =
      ∑ k ∈ majorArcs n, rawVonMangoldtDftSquareFourierTerm n k := by
  simp [rawVonMangoldtFourierMajorArcComplexContribution,
    zmodMajorArcContribution,
    rawVonMangoldtDftSquareFourierTerm_eq_zmodFourierTerm]

theorem
    rawVonMangoldtFourierMajorArcComplexContribution_norm_sub_model_sum_le_of_dft_square_term_approx_bound
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat)
    {majorArcModelTerm : ZMod n.succ → ℂ}
    {majorArcTermError : ZMod n.succ → ℝ}
    (hterm :
      ∀ k ∈ majorArcs n,
        ‖rawVonMangoldtDftSquareFourierTerm n k -
            majorArcModelTerm k‖ ≤ majorArcTermError k) :
    ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
        ∑ k ∈ majorArcs n, majorArcModelTerm k‖ ≤
      ∑ k ∈ majorArcs n, majorArcTermError k := by
  rw [rawVonMangoldtFourierMajorArcComplexContribution_eq_dft_square_sum]
  have hdiff :
      (∑ k ∈ majorArcs n, rawVonMangoldtDftSquareFourierTerm n k) -
          ∑ k ∈ majorArcs n, majorArcModelTerm k =
        ∑ k ∈ majorArcs n,
          (rawVonMangoldtDftSquareFourierTerm n k -
            majorArcModelTerm k) := by
    rw [Finset.sum_sub_distrib]
  calc
    ‖(∑ k ∈ majorArcs n, rawVonMangoldtDftSquareFourierTerm n k) -
        ∑ k ∈ majorArcs n, majorArcModelTerm k‖
        = ‖∑ k ∈ majorArcs n,
            (rawVonMangoldtDftSquareFourierTerm n k -
              majorArcModelTerm k)‖ := by
          rw [hdiff]
    _ ≤ ∑ k ∈ majorArcs n,
          ‖rawVonMangoldtDftSquareFourierTerm n k -
            majorArcModelTerm k‖ :=
        norm_sum_le (majorArcs n)
          (fun k =>
            rawVonMangoldtDftSquareFourierTerm n k -
              majorArcModelTerm k)
    _ ≤ ∑ k ∈ majorArcs n, majorArcTermError k :=
        Finset.sum_le_sum hterm

theorem majorArcComplexApproximationBound_of_dft_square_term_approximation
    {majorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {majorArcError majorArcModelError : Nat → ℝ}
    {majorArcModelTerm : (n : Nat) → ZMod n.succ → ℂ}
    {majorArcTermError : (n : Nat) → ZMod n.succ → ℝ}
    (hterm :
      ∀ n : Nat, majorArcThreshold < n → Even n →
        ∀ k ∈ majorArcs n,
          ‖rawVonMangoldtDftSquareFourierTerm n k -
              majorArcModelTerm n k‖ ≤ majorArcTermError n k)
    (hmodel :
      ∀ n : Nat, majorArcThreshold < n → Even n →
        ‖(∑ k ∈ majorArcs n, majorArcModelTerm n k) -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          majorArcModelError n)
    (hmajorError :
      ∀ n : Nat, majorArcThreshold < n → Even n →
        (∑ k ∈ majorArcs n, majorArcTermError n k) +
          majorArcModelError n ≤ majorArcError n) :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        majorArcError n := by
  intro n hn hEven
  have hterm_sum :
      ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          ∑ k ∈ majorArcs n, majorArcModelTerm n k‖ ≤
        ∑ k ∈ majorArcs n, majorArcTermError n k :=
    rawVonMangoldtFourierMajorArcComplexContribution_norm_sub_model_sum_le_of_dft_square_term_approx_bound
      (majorArcs := majorArcs) (n := n)
      (majorArcModelTerm := majorArcModelTerm n)
      (majorArcTermError := majorArcTermError n)
      (hterm n hn hEven)
  have hmodel_n := hmodel n hn hEven
  have hsplit :
      rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ) =
        (rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            ∑ k ∈ majorArcs n, majorArcModelTerm n k) +
          ((∑ k ∈ majorArcs n, majorArcModelTerm n k) -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)) := by
    ring
  calc
    ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
        (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖
        = ‖(rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            ∑ k ∈ majorArcs n, majorArcModelTerm n k) +
          ((∑ k ∈ majorArcs n, majorArcModelTerm n k) -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ))‖ := by
          rw [hsplit]
    _ ≤ ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
            ∑ k ∈ majorArcs n, majorArcModelTerm n k‖ +
          ‖(∑ k ∈ majorArcs n, majorArcModelTerm n k) -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ (∑ k ∈ majorArcs n, majorArcTermError n k) +
          majorArcModelError n :=
        add_le_add hterm_sum hmodel_n
    _ ≤ majorArcError n := hmajorError n hn hEven

theorem
    majorArcComplexApproximationBound_of_dft_square_term_approximation_exact_model
    {majorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {majorArcError : Nat → ℝ}
    {majorArcModelTerm : (n : Nat) → ZMod n.succ → ℂ}
    {majorArcTermError : (n : Nat) → ZMod n.succ → ℝ}
    (hterm :
      ∀ n : Nat, majorArcThreshold < n → Even n →
        ∀ k ∈ majorArcs n,
          ‖rawVonMangoldtDftSquareFourierTerm n k -
              majorArcModelTerm n k‖ ≤ majorArcTermError n k)
    (hmodel :
      ∀ n : Nat, majorArcThreshold < n → Even n →
        (∑ k ∈ majorArcs n, majorArcModelTerm n k) =
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ))
    (hmajorError :
      ∀ n : Nat, majorArcThreshold < n → Even n →
        (∑ k ∈ majorArcs n, majorArcTermError n k) ≤
          majorArcError n) :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        majorArcError n := by
  refine
    majorArcComplexApproximationBound_of_dft_square_term_approximation
      (majorArcs := majorArcs)
      (majorArcError := majorArcError)
      (majorArcModelError := fun _ => 0)
      (majorArcModelTerm := majorArcModelTerm)
      (majorArcTermError := majorArcTermError)
      hterm ?_ ?_
  · intro n hn hEven
    rw [hmodel n hn hEven]
    simp
  · intro n hn hEven
    simpa using hmajorError n hn hEven

theorem rawVonMangoldtFourierMinorArcComplexContribution_eq_dft_square_sum
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) :
    rawVonMangoldtFourierMinorArcComplexContribution majorArcs n =
      ∑ k ∈ zmodMinorFrequencies (majorArcs n),
        rawVonMangoldtDftSquareFourierTerm n k := by
  simp [rawVonMangoldtFourierMinorArcComplexContribution,
    zmodMinorArcContribution, zmodMinorFrequencies,
    rawVonMangoldtDftSquareFourierTerm_eq_zmodFourierTerm]

theorem rawVonMangoldtFourierMinorArcComplexContribution_norm_le_sum_norm
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) :
    ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
      ∑ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖rawVonMangoldtDftSquareFourierTerm n k‖ := by
  simpa [rawVonMangoldtFourierMinorArcComplexContribution,
    rawVonMangoldtDftSquareFourierTerm_eq_zmodFourierTerm] using
    zmodMinorArcContribution_norm_le_sum_norm
      (vonMangoldtZModWeight n.succ)
      (vonMangoldtZModWeight n.succ)
      (majorArcs n)
      (n : ZMod n.succ)

theorem
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_inv_mul_sum_dft_norm_sq
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) :
    ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
      ‖((n.succ : ℂ)⁻¹)‖ *
        ∑ k ∈ zmodMinorFrequencies (majorArcs n),
          ‖vonMangoldtZModDft n k‖ ^ 2 := by
  have hminor :=
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_sum_norm
      majorArcs n
  calc
    ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖
        ≤ ∑ k ∈ zmodMinorFrequencies (majorArcs n),
            ‖rawVonMangoldtDftSquareFourierTerm n k‖ := hminor
    _ = ‖((n.succ : ℂ)⁻¹)‖ *
        ∑ k ∈ zmodMinorFrequencies (majorArcs n),
          ‖vonMangoldtZModDft n k‖ ^ 2 := by
        simp [rawVonMangoldtDftSquareFourierTerm_norm,
          Finset.mul_sum]

theorem
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_square_term_bound
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat)
    {termBound : ZMod n.succ → ℝ}
    (hterm :
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖rawVonMangoldtDftSquareFourierTerm n k‖ ≤ termBound k) :
    ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
      ∑ k ∈ zmodMinorFrequencies (majorArcs n), termBound k :=
  (rawVonMangoldtFourierMinorArcComplexContribution_norm_le_sum_norm
    majorArcs n).trans (Finset.sum_le_sum hterm)

theorem
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_inv_mul_sum_dft_bound_sq
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat)
    {dftBound : ZMod n.succ → ℝ}
    (hdft :
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ dftBound k) :
    ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
      ‖((n.succ : ℂ)⁻¹)‖ *
        ∑ k ∈ zmodMinorFrequencies (majorArcs n),
          dftBound k ^ 2 := by
  have hminor :=
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_inv_mul_sum_dft_norm_sq
      majorArcs n
  have hsum :
      (∑ k ∈ zmodMinorFrequencies (majorArcs n),
          ‖vonMangoldtZModDft n k‖ ^ 2) ≤
        ∑ k ∈ zmodMinorFrequencies (majorArcs n),
          dftBound k ^ 2 := by
    exact Finset.sum_le_sum (by
      intro k hk
      nlinarith [hdft k hk, norm_nonneg (vonMangoldtZModDft n k)])
  exact hminor.trans (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))

theorem
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_bound
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat)
    {dftBound : ℝ}
    (hdftBound_nonneg : 0 ≤ dftBound)
    (hdft :
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ dftBound) :
    ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
      ((zmodMinorFrequencies (majorArcs n)).card : ℝ) *
        (‖((n.succ : ℂ)⁻¹)‖ * dftBound ^ 2) := by
  let termBound : ZMod n.succ → ℝ :=
    fun _ => ‖((n.succ : ℂ)⁻¹)‖ * dftBound ^ 2
  have hterm :
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖rawVonMangoldtDftSquareFourierTerm n k‖ ≤ termBound k := by
    intro k hk
    rw [rawVonMangoldtDftSquareFourierTerm_norm]
    have hsq :
        ‖vonMangoldtZModDft n k‖ ^ 2 ≤ dftBound ^ 2 := by
      nlinarith [hdft k hk, norm_nonneg (vonMangoldtZModDft n k),
        hdftBound_nonneg]
    exact mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
  have hminor :=
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_square_term_bound
      (majorArcs := majorArcs) (n := n) (termBound := termBound)
      hterm
  simpa [termBound, Finset.sum_const, nsmul_eq_mul] using hminor

theorem minorArcDftBoundValid_of_not_mem_majorArcs
    {minorArcThreshold : Nat}
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    {minorArcDftBound : Nat → ℝ}
    (hdft :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ∀ k : ZMod n.succ, k ∉ majorArcs n →
          ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n := by
  intro n hn hEven k hk
  exact hdft n hn hEven k (mem_zmodMinorFrequencies.mp hk)

theorem minorArcDftBoundValid_of_ne_zero_of_zero_mem_majorArcs
    {minorArcThreshold : Nat}
    {majorArcs : (n : Nat) → Finset (ZMod n.succ)}
    {minorArcDftBound : Nat → ℝ}
    (hzero :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        (0 : ZMod n.succ) ∈ majorArcs n)
    (hdft :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ∀ k : ZMod n.succ, k ≠ 0 →
          ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n := by
  intro n hn hEven k hk
  refine hdft n hn hEven k ?_
  intro hkzero
  have hk_not_major : k ∉ majorArcs n :=
    mem_zmodMinorFrequencies.mp hk
  exact hk_not_major (by simpa [hkzero] using hzero n hn hEven)

theorem
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_bound_and_card_bound
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat)
    {dftBound frequencyCountBound : ℝ}
    (hdftBound_nonneg : 0 ≤ dftBound)
    (hdft :
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ dftBound)
    (hcard :
      ((zmodMinorFrequencies (majorArcs n)).card : ℝ) ≤
        frequencyCountBound) :
    ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
      frequencyCountBound * (‖((n.succ : ℂ)⁻¹)‖ * dftBound ^ 2) := by
  have hminor :=
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_bound
      majorArcs n hdftBound_nonneg hdft
  have hfactor_nonneg :
      0 ≤ ‖((n.succ : ℂ)⁻¹)‖ * dftBound ^ 2 := by positivity
  exact hminor.trans (mul_le_mul_of_nonneg_right hcard hfactor_nonneg)

theorem
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_dft_bound_sq
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat)
    {dftBound : ℝ}
    (hdftBound_nonneg : 0 ≤ dftBound)
    (hdft :
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ dftBound) :
    ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
      dftBound ^ 2 := by
  have hcard :
      ((zmodMinorFrequencies (majorArcs n)).card : ℝ) ≤
        (n.succ : ℝ) :=
    zmodMinorFrequencies_card_real_le (majorArcs n)
  have hminor :=
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_bound_and_card_bound
      (majorArcs := majorArcs) (n := n)
      (dftBound := dftBound) (frequencyCountBound := (n.succ : ℝ))
      hdftBound_nonneg hdft hcard
  have hnormalized :
      (n.succ : ℝ) * (‖((n.succ : ℂ)⁻¹)‖ * dftBound ^ 2) =
        dftBound ^ 2 := by
    have hnpos : (0 : ℝ) < n.succ := by positivity
    calc
      (n.succ : ℝ) * (‖((n.succ : ℂ)⁻¹)‖ * dftBound ^ 2)
          = ((n.succ : ℝ) * ((n.succ : ℝ)⁻¹)) *
              dftBound ^ 2 := by
            rw [norm_inv, Complex.norm_natCast]
            ring
      _ = dftBound ^ 2 := by
            rw [mul_inv_cancel₀ hnpos.ne']
            ring
  exact hminor.trans_eq hnormalized

theorem
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_dft_bound_sq_of_uniform_bound
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat)
    {dftBound : ℝ}
    (hdft :
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ dftBound) :
    ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
      dftBound ^ 2 := by
  have hminor :=
    rawVonMangoldtFourierMinorArcComplexContribution_norm_le_inv_mul_sum_dft_bound_sq
      (majorArcs := majorArcs) (n := n)
      (dftBound := fun _ => dftBound)
      hdft
  have hcard :
      ((zmodMinorFrequencies (majorArcs n)).card : ℝ) ≤
        (n.succ : ℝ) :=
    zmodMinorFrequencies_card_real_le (majorArcs n)
  have hsum :
      ‖((n.succ : ℂ)⁻¹)‖ *
          (∑ _ ∈ zmodMinorFrequencies (majorArcs n), dftBound ^ 2) ≤
        ‖((n.succ : ℂ)⁻¹)‖ * ((n.succ : ℝ) * dftBound ^ 2) := by
    have hsquare_nonneg : 0 ≤ dftBound ^ 2 := by positivity
    have hsum_le :
        (∑ _ ∈ zmodMinorFrequencies (majorArcs n), dftBound ^ 2) ≤
          (n.succ : ℝ) * dftBound ^ 2 := by
      simpa [Finset.sum_const, nsmul_eq_mul] using
        (mul_le_mul_of_nonneg_right hcard hsquare_nonneg)
    exact mul_le_mul_of_nonneg_left hsum_le (norm_nonneg _)
  have hnormalized :
      ‖((n.succ : ℂ)⁻¹)‖ * ((n.succ : ℝ) * dftBound ^ 2) =
        dftBound ^ 2 := by
    have hnpos : (0 : ℝ) < n.succ := by positivity
    calc
      ‖((n.succ : ℂ)⁻¹)‖ * ((n.succ : ℝ) * dftBound ^ 2)
          = ((n.succ : ℝ) * ((n.succ : ℝ)⁻¹)) *
              dftBound ^ 2 := by
            rw [norm_inv, Complex.norm_natCast]
            ring
      _ = dftBound ^ 2 := by
            rw [mul_inv_cancel₀ hnpos.ne']
            ring
  exact hminor.trans (hsum.trans_eq hnormalized)

theorem minorArcComplexContributionBound_of_dft_square_term_bound
    {minorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {minorArcError : Nat → ℝ}
    {minorArcTermBound : (n : Nat) → ZMod n.succ → ℝ}
    (hterm :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ∀ k ∈ zmodMinorFrequencies (majorArcs n),
          ‖rawVonMangoldtDftSquareFourierTerm n k‖ ≤
            minorArcTermBound n k)
    (hsum :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        (∑ k ∈ zmodMinorFrequencies (majorArcs n),
          minorArcTermBound n k) ≤ minorArcError n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n := by
  intro n hn hEven
  exact
    (rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_square_term_bound
      majorArcs n (hterm n hn hEven)).trans
      (hsum n hn hEven)

theorem minorArcComplexContributionBound_of_dft_norm_sq_sum
    {minorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {minorArcError : Nat → ℝ}
    (hminorError :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ‖((n.succ : ℂ)⁻¹)‖ *
          (∑ k ∈ zmodMinorFrequencies (majorArcs n),
            ‖vonMangoldtZModDft n k‖ ^ 2) ≤ minorArcError n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n := by
  intro n hn hEven
  exact
    (rawVonMangoldtFourierMinorArcComplexContribution_norm_le_inv_mul_sum_dft_norm_sq
      majorArcs n).trans
      (hminorError n hn hEven)

theorem minorArcComplexContributionBound_of_dft_bound_sum_sq
    {minorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {minorArcDftBound : (n : Nat) → ZMod n.succ → ℝ}
    {minorArcError : Nat → ℝ}
    (hdft :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ∀ k ∈ zmodMinorFrequencies (majorArcs n),
          ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n k)
    (hminorError :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ‖((n.succ : ℂ)⁻¹)‖ *
          (∑ k ∈ zmodMinorFrequencies (majorArcs n),
            minorArcDftBound n k ^ 2) ≤ minorArcError n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n := by
  intro n hn hEven
  exact
    (rawVonMangoldtFourierMinorArcComplexContribution_norm_le_inv_mul_sum_dft_bound_sq
      majorArcs n
      (hdft n hn hEven)).trans
      (hminorError n hn hEven)

theorem minorArcComplexContributionBound_of_dft_bound
    {minorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {minorArcDftBound minorArcError : Nat → ℝ}
    (hdftBound_nonneg :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        0 ≤ minorArcDftBound n)
    (hdft :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ∀ k ∈ zmodMinorFrequencies (majorArcs n),
          ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n)
    (hminorError :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ((zmodMinorFrequencies (majorArcs n)).card : ℝ) *
          (‖((n.succ : ℂ)⁻¹)‖ * minorArcDftBound n ^ 2) ≤
            minorArcError n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n := by
  intro n hn hEven
  exact
    (rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_bound
      majorArcs n (hdftBound_nonneg n hn hEven)
      (hdft n hn hEven)).trans
      (hminorError n hn hEven)

theorem minorArcComplexContributionBound_of_dft_bound_and_card_bound
    {minorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {minorArcDftBound minorArcFrequencyCountBound minorArcError :
      Nat → ℝ}
    (hdftBound_nonneg :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        0 ≤ minorArcDftBound n)
    (hdft :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ∀ k ∈ zmodMinorFrequencies (majorArcs n),
          ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n)
    (hcard :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ((zmodMinorFrequencies (majorArcs n)).card : ℝ) ≤
          minorArcFrequencyCountBound n)
    (hminorError :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        minorArcFrequencyCountBound n *
          (‖((n.succ : ℂ)⁻¹)‖ * minorArcDftBound n ^ 2) ≤
            minorArcError n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n := by
  intro n hn hEven
  exact
    (rawVonMangoldtFourierMinorArcComplexContribution_norm_le_of_dft_bound_and_card_bound
      majorArcs n (hdftBound_nonneg n hn hEven)
      (hdft n hn hEven) (hcard n hn hEven)).trans
      (hminorError n hn hEven)

theorem minorArcComplexContributionBound_of_dft_bound_sq
    {minorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {minorArcDftBound minorArcError : Nat → ℝ}
    (hdftBound_nonneg :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        0 ≤ minorArcDftBound n)
    (hdft :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ∀ k ∈ zmodMinorFrequencies (majorArcs n),
          ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n)
    (hminorError :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        minorArcDftBound n ^ 2 ≤ minorArcError n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n := by
  intro n hn hEven
  exact
    (rawVonMangoldtFourierMinorArcComplexContribution_norm_le_dft_bound_sq
      majorArcs n (hdftBound_nonneg n hn hEven)
      (hdft n hn hEven)).trans
      (hminorError n hn hEven)

theorem minorArcComplexContributionBound_of_dft_bound_sq_of_uniform_bound
    {minorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {minorArcDftBound minorArcError : Nat → ℝ}
    (hdft :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ∀ k ∈ zmodMinorFrequencies (majorArcs n),
          ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n)
    (hminorError :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        minorArcDftBound n ^ 2 ≤ minorArcError n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n := by
  intro n hn hEven
  exact
    (rawVonMangoldtFourierMinorArcComplexContribution_norm_le_dft_bound_sq_of_uniform_bound
      majorArcs n (hdft n hn hEven)).trans
      (hminorError n hn hEven)

theorem minorArcDftSquareSumBound_of_uniform_bound_and_card_bound
    {minorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {minorArcDftBound minorArcFrequencyCountBound minorArcError :
      Nat → ℝ}
    (hcard :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ((zmodMinorFrequencies (majorArcs n)).card : ℝ) ≤
          minorArcFrequencyCountBound n)
    (hminorError :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        minorArcFrequencyCountBound n *
          (‖((n.succ : ℂ)⁻¹)‖ * minorArcDftBound n ^ 2) ≤
            minorArcError n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖((n.succ : ℂ)⁻¹)‖ *
        (∑ _ ∈ zmodMinorFrequencies (majorArcs n),
          minorArcDftBound n ^ 2) ≤ minorArcError n := by
  intro n hn hEven
  have hfactor_nonneg :
      0 ≤ ‖((n.succ : ℂ)⁻¹)‖ * minorArcDftBound n ^ 2 := by
    positivity
  have hcard_mul :
      ((zmodMinorFrequencies (majorArcs n)).card : ℝ) *
          (‖((n.succ : ℂ)⁻¹)‖ * minorArcDftBound n ^ 2) ≤
        minorArcFrequencyCountBound n *
          (‖((n.succ : ℂ)⁻¹)‖ * minorArcDftBound n ^ 2) :=
    mul_le_mul_of_nonneg_right (hcard n hn hEven) hfactor_nonneg
  calc
    ‖((n.succ : ℂ)⁻¹)‖ *
        (∑ _ ∈ zmodMinorFrequencies (majorArcs n),
          minorArcDftBound n ^ 2)
        = ((zmodMinorFrequencies (majorArcs n)).card : ℝ) *
            (‖((n.succ : ℂ)⁻¹)‖ * minorArcDftBound n ^ 2) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm]
    _ ≤ minorArcFrequencyCountBound n *
          (‖((n.succ : ℂ)⁻¹)‖ * minorArcDftBound n ^ 2) :=
        hcard_mul
    _ ≤ minorArcError n := hminorError n hn hEven

noncomputable def rawVonMangoldtFourierMajorArcContribution
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) : ℝ :=
  (rawVonMangoldtFourierMajorArcComplexContribution majorArcs n).re

noncomputable def rawVonMangoldtFourierMinorArcContribution
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) : ℝ :=
  (rawVonMangoldtFourierMinorArcComplexContribution majorArcs n).re

theorem rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor
    (majorArcs : (n : Nat) → Finset (ZMod n.succ)) (n : Nat) :
    RawVonMangoldtGoldbachSum n =
      rawVonMangoldtFourierMajorArcContribution majorArcs n +
        rawVonMangoldtFourierMinorArcContribution majorArcs n := by
  have hcomplex :=
    rawVonMangoldtGoldbachSum_complex_eq_fourier_major_add_minor
      n (majorArcs n)
  have hre := congrArg Complex.re hcomplex
  simpa [rawVonMangoldtFourierMajorArcContribution,
    rawVonMangoldtFourierMinorArcContribution,
    rawVonMangoldtFourierMajorArcComplexContribution,
    rawVonMangoldtFourierMinorArcComplexContribution] using hre

theorem real_abs_re_sub_le_complex_norm_sub_real
    (z : ℂ) (x : ℝ) :
    |z.re - x| ≤ ‖z - (x : ℂ)‖ := by
  simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - (x : ℂ))

theorem real_abs_re_sub_mul_le_complex_norm_sub_ofReal_mul
    (z : ℂ) (x y : ℝ) :
    |z.re - x * y| ≤ ‖z - ((x : ℂ) * (y : ℂ))‖ := by
  simpa [Complex.sub_re] using
    Complex.abs_re_le_norm (z - ((x : ℂ) * (y : ℂ)))

theorem real_abs_re_le_complex_norm (z : ℂ) :
    |z.re| ≤ ‖z‖ :=
  Complex.abs_re_le_norm z

structure VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  totalLinearErrorThreshold : Nat
  relativeError : ℝ
  relativeError_nonneg : 0 ≤ relativeError
  relativeError_lt_one : relativeError < 1
  analyticErrorCoefficient : ℝ
  analyticErrorCoefficient_le_quarter :
    analyticErrorCoefficient ≤ relativeError * (1 / 4 : ℝ)
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  majorArcApproximationBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      |rawVonMangoldtFourierMajorArcContribution majorArcs n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
        majorArcError n
  minorArcContributionBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      |rawVonMangoldtFourierMinorArcContribution majorArcs n| ≤
        minorArcError n
  totalLinearErrorBound :
    ∀ n : Nat, totalLinearErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤
        analyticErrorCoefficient * (n : ℝ)

noncomputable def
    VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate.toLinearErrorDecomposition
    (estimate :
      VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate) :
    VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate where
  decompositionThreshold := 0
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  totalLinearErrorThreshold := estimate.totalLinearErrorThreshold
  relativeError := estimate.relativeError
  relativeError_nonneg := estimate.relativeError_nonneg
  relativeError_lt_one := estimate.relativeError_lt_one
  analyticErrorCoefficient := estimate.analyticErrorCoefficient
  analyticErrorCoefficient_le_quarter :=
    estimate.analyticErrorCoefficient_le_quarter
  majorArcContribution :=
    rawVonMangoldtFourierMajorArcContribution estimate.majorArcs
  minorArcContribution :=
    rawVonMangoldtFourierMinorArcContribution estimate.majorArcs
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  rawDecomposition := by
    intro n _hn _hEven
    exact rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor
      estimate.majorArcs n
  majorArcApproximationBound := estimate.majorArcApproximationBound
  minorArcContributionBound := estimate.minorArcContributionBound
  totalLinearErrorBound := estimate.totalLinearErrorBound

noncomputable def
    VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toLinearErrorDecomposition.canonicalContaminationThreshold

noncomputable def
    VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toLinearErrorDecomposition.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (htotal : estimate.totalLinearErrorThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toLinearErrorDecomposition.directRawWeightSumThreshold_le_of_components
    (Nat.zero_le B) hmajor hminor htotal hcontamination

theorem
    count_positive_above_of_vonMangoldt_fourier_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_linear_error_decomposition_canonical_weight_sum_estimate
    estimate.toLinearErrorDecomposition

theorem
    explicit_lower_bound_of_vonMangoldt_fourier_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_quarter_linear_error_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_fourier_quarter_linear_error_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_linear_error_decomposition_canonical_weight_sum_estimate_le
    finite
    estimate.toLinearErrorDecomposition
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_fourier_quarter_linear_error_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_quarter_linear_error_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  totalLinearErrorThreshold : Nat
  relativeError : ℝ
  relativeError_nonneg : 0 ≤ relativeError
  relativeError_lt_one : relativeError < 1
  analyticErrorCoefficient : ℝ
  analyticErrorCoefficient_le_quarter :
    analyticErrorCoefficient ≤ relativeError * (1 / 4 : ℝ)
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  majorArcComplexApproximationBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMajorArcComplexContribution majorArcs n -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        majorArcError n
  minorArcComplexContributionBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n
  totalLinearErrorBound :
    ∀ n : Nat, totalLinearErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤
        analyticErrorCoefficient * (n : ℝ)

noncomputable def
    VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate.toFourierQuarterLinearErrorCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate) :
    VonMangoldtFourierQuarterLinearErrorCanonicalWeightSumEstimate where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  totalLinearErrorThreshold := estimate.totalLinearErrorThreshold
  relativeError := estimate.relativeError
  relativeError_nonneg := estimate.relativeError_nonneg
  relativeError_lt_one := estimate.relativeError_lt_one
  analyticErrorCoefficient := estimate.analyticErrorCoefficient
  analyticErrorCoefficient_le_quarter :=
    estimate.analyticErrorCoefficient_le_quarter
  majorArcs := estimate.majorArcs
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  majorArcApproximationBound := by
    intro n hn hEven
    have hcomplex :=
      estimate.majorArcComplexApproximationBound n hn hEven
    have hcomplex' :
        ‖rawVonMangoldtFourierMajorArcComplexContribution estimate.majorArcs n -
            (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
          estimate.majorArcError n := by
      simpa using hcomplex
    exact
      (real_abs_re_sub_mul_le_complex_norm_sub_ofReal_mul
        (rawVonMangoldtFourierMajorArcComplexContribution
          estimate.majorArcs n)
        (goldbachSingularSeriesFromQuarter n)
        (n : ℝ)).trans
        hcomplex'
  minorArcContributionBound := by
    intro n hn hEven
    have hcomplex :=
      estimate.minorArcComplexContributionBound n hn hEven
    exact
      (real_abs_re_le_complex_norm
        (rawVonMangoldtFourierMinorArcComplexContribution
          estimate.majorArcs n)).trans hcomplex
  totalLinearErrorBound := estimate.totalLinearErrorBound

noncomputable def
    VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toFourierQuarterLinearErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold

noncomputable def
    VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toFourierQuarterLinearErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (htotal : estimate.totalLinearErrorThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toFourierQuarterLinearErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    hmajor hminor htotal hcontamination

theorem
    count_positive_above_of_vonMangoldt_fourier_complex_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_quarter_linear_error_canonical_weight_sum_estimate
    estimate.toFourierQuarterLinearErrorCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_fourier_complex_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_complex_quarter_linear_error_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_fourier_complex_quarter_linear_error_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_quarter_linear_error_canonical_weight_sum_estimate_le
    finite
    estimate.toFourierQuarterLinearErrorCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_fourier_complex_quarter_linear_error_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_complex_quarter_linear_error_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  totalLinearErrorThreshold : Nat
  relativeError : ℝ
  relativeError_nonneg : 0 ≤ relativeError
  relativeError_lt_one : relativeError < 1
  analyticErrorCoefficient : ℝ
  analyticErrorCoefficient_le_quarter :
    analyticErrorCoefficient ≤ relativeError * (1 / 4 : ℝ)
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  majorArcModelTerm : (n : Nat) → ZMod n.succ → ℂ
  majorArcTermError : (n : Nat) → ZMod n.succ → ℝ
  majorArcModelError : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcDftBound : (n : Nat) → ZMod n.succ → ℝ
  minorArcError : Nat → ℝ
  majorArcTermApproximationBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      ∀ k ∈ majorArcs n,
        ‖rawVonMangoldtDftSquareFourierTerm n k -
            majorArcModelTerm n k‖ ≤ majorArcTermError n k
  majorArcModelApproximationBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      ‖(∑ k ∈ majorArcs n, majorArcModelTerm n k) -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        majorArcModelError n
  majorArcErrorBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      (∑ k ∈ majorArcs n, majorArcTermError n k) +
        majorArcModelError n ≤ majorArcError n
  minorArcDftBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n k
  minorArcSquareSumBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖((n.succ : ℂ)⁻¹)‖ *
        (∑ k ∈ zmodMinorFrequencies (majorArcs n),
          minorArcDftBound n k ^ 2) ≤ minorArcError n
  totalLinearErrorBound :
    ∀ n : Nat, totalLinearErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤
        analyticErrorCoefficient * (n : ℝ)

structure
    VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  totalLinearErrorThreshold : Nat
  relativeError : ℝ
  relativeError_nonneg : 0 ≤ relativeError
  relativeError_lt_one : relativeError < 1
  analyticErrorCoefficient : ℝ
  analyticErrorCoefficient_le_quarter :
    analyticErrorCoefficient ≤ relativeError * (1 / 4 : ℝ)
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  majorArcModelTerm : (n : Nat) → ZMod n.succ → ℂ
  majorArcTermError : (n : Nat) → ZMod n.succ → ℝ
  majorArcModelError : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcDftBound : Nat → ℝ
  minorArcFrequencyCountBound : Nat → ℝ
  minorArcError : Nat → ℝ
  majorArcTermApproximationBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      ∀ k ∈ majorArcs n,
        ‖rawVonMangoldtDftSquareFourierTerm n k -
            majorArcModelTerm n k‖ ≤ majorArcTermError n k
  majorArcModelApproximationBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      ‖(∑ k ∈ majorArcs n, majorArcModelTerm n k) -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        majorArcModelError n
  majorArcErrorBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      (∑ k ∈ majorArcs n, majorArcTermError n k) +
        majorArcModelError n ≤ majorArcError n
  minorArcDftBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n
  minorArcFrequencyCountBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ((zmodMinorFrequencies (majorArcs n)).card : ℝ) ≤
        minorArcFrequencyCountBound n
  minorArcSquareSumErrorBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      minorArcFrequencyCountBound n *
        (‖((n.succ : ℂ)⁻¹)‖ * minorArcDftBound n ^ 2) ≤
          minorArcError n
  totalLinearErrorBound :
    ∀ n : Nat, totalLinearErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤
        analyticErrorCoefficient * (n : ℝ)

structure
    VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  totalLinearErrorThreshold : Nat
  relativeError : ℝ
  relativeError_nonneg : 0 ≤ relativeError
  relativeError_lt_one : relativeError < 1
  analyticErrorCoefficient : ℝ
  analyticErrorCoefficient_le_quarter :
    analyticErrorCoefficient ≤ relativeError * (1 / 4 : ℝ)
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  majorArcModelTerm : (n : Nat) → ZMod n.succ → ℂ
  majorArcTermError : (n : Nat) → ZMod n.succ → ℝ
  majorArcModelError : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcDftBound : Nat → ℝ
  minorArcError : Nat → ℝ
  majorArcTermApproximationBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      ∀ k ∈ majorArcs n,
        ‖rawVonMangoldtDftSquareFourierTerm n k -
            majorArcModelTerm n k‖ ≤ majorArcTermError n k
  majorArcModelApproximationBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      ‖(∑ k ∈ majorArcs n, majorArcModelTerm n k) -
          (goldbachSingularSeriesFromQuarter n * (n : ℝ) : ℂ)‖ ≤
        majorArcModelError n
  majorArcErrorBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      (∑ k ∈ majorArcs n, majorArcTermError n k) +
        majorArcModelError n ≤ majorArcError n
  minorArcDftBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n
  minorArcDftBoundSqErrorBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      minorArcDftBound n ^ 2 ≤ minorArcError n
  totalLinearErrorBound :
    ∀ n : Nat, totalLinearErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤
        analyticErrorCoefficient * (n : ℝ)

noncomputable def
    VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate) :
    VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  totalLinearErrorThreshold := estimate.totalLinearErrorThreshold
  relativeError := estimate.relativeError
  relativeError_nonneg := estimate.relativeError_nonneg
  relativeError_lt_one := estimate.relativeError_lt_one
  analyticErrorCoefficient := estimate.analyticErrorCoefficient
  analyticErrorCoefficient_le_quarter :=
    estimate.analyticErrorCoefficient_le_quarter
  majorArcs := estimate.majorArcs
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  majorArcComplexApproximationBound :=
    majorArcComplexApproximationBound_of_dft_square_term_approximation
      (majorArcs := estimate.majorArcs)
      (majorArcError := estimate.majorArcError)
      (majorArcModelError := estimate.majorArcModelError)
      (majorArcModelTerm := estimate.majorArcModelTerm)
      (majorArcTermError := estimate.majorArcTermError)
      estimate.majorArcTermApproximationBound
      estimate.majorArcModelApproximationBound
      estimate.majorArcErrorBound
  minorArcComplexContributionBound :=
    minorArcComplexContributionBound_of_dft_bound_sum_sq
      (majorArcs := estimate.majorArcs)
      (minorArcDftBound := estimate.minorArcDftBound)
      (minorArcError := estimate.minorArcError)
      estimate.minorArcDftBoundValid
      estimate.minorArcSquareSumBound
  totalLinearErrorBound := estimate.totalLinearErrorBound

noncomputable def
    VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate.toDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate) :
    VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  totalLinearErrorThreshold := estimate.totalLinearErrorThreshold
  relativeError := estimate.relativeError
  relativeError_nonneg := estimate.relativeError_nonneg
  relativeError_lt_one := estimate.relativeError_lt_one
  analyticErrorCoefficient := estimate.analyticErrorCoefficient
  analyticErrorCoefficient_le_quarter :=
    estimate.analyticErrorCoefficient_le_quarter
  majorArcs := estimate.majorArcs
  majorArcModelTerm := estimate.majorArcModelTerm
  majorArcTermError := estimate.majorArcTermError
  majorArcModelError := estimate.majorArcModelError
  majorArcError := estimate.majorArcError
  minorArcDftBound := fun n _ => estimate.minorArcDftBound n
  minorArcError := estimate.minorArcError
  majorArcTermApproximationBound :=
    estimate.majorArcTermApproximationBound
  majorArcModelApproximationBound :=
    estimate.majorArcModelApproximationBound
  majorArcErrorBound := estimate.majorArcErrorBound
  minorArcDftBoundValid := by
    intro n hn hEven k hk
    exact estimate.minorArcDftBoundValid n hn hEven k hk
  minorArcSquareSumBound :=
    minorArcDftSquareSumBound_of_uniform_bound_and_card_bound
      estimate.majorArcs
      estimate.minorArcFrequencyCountBoundValid
      estimate.minorArcSquareSumErrorBound
  totalLinearErrorBound := estimate.totalLinearErrorBound

noncomputable def
    VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate) :
    VonMangoldtFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  totalLinearErrorThreshold := estimate.totalLinearErrorThreshold
  relativeError := estimate.relativeError
  relativeError_nonneg := estimate.relativeError_nonneg
  relativeError_lt_one := estimate.relativeError_lt_one
  analyticErrorCoefficient := estimate.analyticErrorCoefficient
  analyticErrorCoefficient_le_quarter :=
    estimate.analyticErrorCoefficient_le_quarter
  majorArcs := estimate.majorArcs
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  majorArcComplexApproximationBound :=
    majorArcComplexApproximationBound_of_dft_square_term_approximation
      (majorArcs := estimate.majorArcs)
      (majorArcError := estimate.majorArcError)
      (majorArcModelError := estimate.majorArcModelError)
      (majorArcModelTerm := estimate.majorArcModelTerm)
      (majorArcTermError := estimate.majorArcTermError)
      estimate.majorArcTermApproximationBound
      estimate.majorArcModelApproximationBound
      estimate.majorArcErrorBound
  minorArcComplexContributionBound :=
    minorArcComplexContributionBound_of_dft_bound_sq_of_uniform_bound
      (majorArcs := estimate.majorArcs)
      (minorArcDftBound := estimate.minorArcDftBound)
      (minorArcError := estimate.minorArcError)
      estimate.minorArcDftBoundValid
      estimate.minorArcDftBoundSqErrorBound
  totalLinearErrorBound := estimate.totalLinearErrorBound

noncomputable def
    VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold

noncomputable def
    VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (htotal : estimate.totalLinearErrorThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    hmajor hminor htotal hcontamination

theorem
    count_positive_above_of_vonMangoldt_dft_model_l2_minor_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_complex_quarter_linear_error_canonical_weight_sum_estimate
    estimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_dft_model_l2_minor_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_model_l2_minor_quarter_linear_error_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_dft_model_l2_minor_quarter_linear_error_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_complex_quarter_linear_error_canonical_weight_sum_estimate_le
    finite
    estimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_dft_model_l2_minor_quarter_linear_error_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_model_l2_minor_quarter_linear_error_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

noncomputable def
    VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold

noncomputable def
    VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (htotal : estimate.totalLinearErrorThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    hmajor hminor htotal hcontamination

theorem
    count_positive_above_of_vonMangoldt_dft_model_uniform_minor_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_model_l2_minor_quarter_linear_error_canonical_weight_sum_estimate
    estimate.toDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_dft_model_uniform_minor_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_model_uniform_minor_quarter_linear_error_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_dft_model_uniform_minor_quarter_linear_error_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_model_l2_minor_quarter_linear_error_canonical_weight_sum_estimate_le
    finite
    estimate.toDftModelL2MinorQuarterLinearErrorCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_dft_model_uniform_minor_quarter_linear_error_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtDftModelUniformMinorQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_model_uniform_minor_quarter_linear_error_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

noncomputable def
    VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold

noncomputable def
    VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (htotal : estimate.totalLinearErrorThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    hmajor hminor htotal hcontamination

theorem
    count_positive_above_of_vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_complex_quarter_linear_error_canonical_weight_sum_estimate
    estimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_complex_quarter_linear_error_canonical_weight_sum_estimate_le
    finite
    estimate.toFourierComplexQuarterLinearErrorCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtDftModelUniformMinorSqQuarterLinearErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_model_uniform_minor_sq_quarter_linear_error_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure VonMangoldtFourierPositiveLinearCanonicalLowerBound where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcError : Nat → ℝ
  majorArcLinearLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcContributionBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      |rawVonMangoldtFourierMinorArcContribution majorArcs n| ≤
        minorArcError n

def VonMangoldtFourierPositiveLinearCanonicalLowerBound.rawThreshold
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound) :
    Nat :=
  max estimate.majorArcThreshold estimate.minorArcThreshold

theorem
    VonMangoldtFourierPositiveLinearCanonicalLowerBound.majorArcThreshold_le_rawThreshold
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound) :
    estimate.majorArcThreshold ≤ estimate.rawThreshold := by
  dsimp [VonMangoldtFourierPositiveLinearCanonicalLowerBound.rawThreshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtFourierPositiveLinearCanonicalLowerBound.minorArcThreshold_le_rawThreshold
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound) :
    estimate.minorArcThreshold ≤ estimate.rawThreshold := by
  dsimp [VonMangoldtFourierPositiveLinearCanonicalLowerBound.rawThreshold]
  exact Nat.le_max_right _ _

noncomputable def
    VonMangoldtFourierPositiveLinearCanonicalLowerBound.toPositiveLinearRawCanonicalWeightSumLowerBound
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound) :
    VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound where
  threshold := estimate.rawThreshold
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  rawLinearLowerBound := by
    intro n hn hEven
    have hmajorThreshold : estimate.majorArcThreshold < n :=
      lt_of_le_of_lt estimate.majorArcThreshold_le_rawThreshold hn
    have hminorThreshold : estimate.minorArcThreshold < n :=
      lt_of_le_of_lt estimate.minorArcThreshold_le_rawThreshold hn
    have hmajor :=
      estimate.majorArcLinearLowerBound n hmajorThreshold hEven
    have hminorAbs :=
      estimate.minorArcContributionBound n hminorThreshold hEven
    have hminorLower :
        -estimate.minorArcError n ≤
          rawVonMangoldtFourierMinorArcContribution estimate.majorArcs n :=
      (abs_le.mp hminorAbs).1
    rw [rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor
      estimate.majorArcs n]
    linarith

noncomputable def
    VonMangoldtFourierPositiveLinearCanonicalLowerBound.canonicalContaminationThreshold
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound) :
    Nat :=
  estimate.toPositiveLinearRawCanonicalWeightSumLowerBound.canonicalContaminationThreshold

noncomputable def
    VonMangoldtFourierPositiveLinearCanonicalLowerBound.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toPositiveLinearRawCanonicalWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtFourierPositiveLinearCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound.directRawWeightSumThreshold_le
    estimate.toPositiveLinearRawCanonicalWeightSumLowerBound
    (max_le hmajor hminor)
    (by
      simpa
        [VonMangoldtFourierPositiveLinearCanonicalLowerBound.canonicalContaminationThreshold]
        using hcontamination)

theorem
    count_positive_above_of_vonMangoldt_fourier_positive_linear_canonical_lower_bound
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound
    estimate.toPositiveLinearRawCanonicalWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_fourier_positive_linear_canonical_lower_bound
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_positive_linear_canonical_lower_bound
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_fourier_positive_linear_canonical_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound_le
    finite
    estimate.toPositiveLinearRawCanonicalWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_fourier_positive_linear_canonical_lower_bound_le100
    (estimate : VonMangoldtFourierPositiveLinearCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_positive_linear_canonical_lower_bound_le
    goldbachUpTo100
    estimate
    hthreshold

structure VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcError : Nat → ℝ
  majorArcLinearLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcComplexContributionBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n

noncomputable def
    VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound.toFourierPositiveLinearCanonicalLowerBound
    (estimate : VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound) :
    VonMangoldtFourierPositiveLinearCanonicalLowerBound where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  majorArcs := estimate.majorArcs
  minorArcError := estimate.minorArcError
  majorArcLinearLowerBound := estimate.majorArcLinearLowerBound
  minorArcContributionBound := by
    intro n hn hEven
    exact
      (real_abs_re_le_complex_norm
        (rawVonMangoldtFourierMinorArcComplexContribution
          estimate.majorArcs n)).trans
        (estimate.minorArcComplexContributionBound n hn hEven)

noncomputable def
    VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound.canonicalContaminationThreshold
    (estimate : VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound) :
    Nat :=
  estimate.toFourierPositiveLinearCanonicalLowerBound.canonicalContaminationThreshold

noncomputable def
    VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toFourierPositiveLinearCanonicalLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate : VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toFourierPositiveLinearCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    hmajor hminor
    (by
      simpa
        [VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound.canonicalContaminationThreshold]
        using hcontamination)

theorem
    count_positive_above_of_vonMangoldt_fourier_complex_positive_linear_canonical_lower_bound
    (estimate : VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_positive_linear_canonical_lower_bound
    estimate.toFourierPositiveLinearCanonicalLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_fourier_complex_positive_linear_canonical_lower_bound
    (estimate : VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_complex_positive_linear_canonical_lower_bound
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_fourier_complex_positive_linear_canonical_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_positive_linear_canonical_lower_bound_le
    finite
    estimate.toFourierPositiveLinearCanonicalLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_fourier_complex_positive_linear_canonical_lower_bound_le100
    (estimate : VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_complex_positive_linear_canonical_lower_bound_le
    goldbachUpTo100
    estimate
    hthreshold

structure VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcDftBound : Nat → ℝ
  minorArcError : Nat → ℝ
  majorArcLinearLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcDftBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n
  minorArcDftBoundSqErrorBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      minorArcDftBound n ^ 2 ≤ minorArcError n

noncomputable def
    VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound.toFourierComplexPositiveLinearCanonicalLowerBound
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound) :
    VonMangoldtFourierComplexPositiveLinearCanonicalLowerBound where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  majorArcs := estimate.majorArcs
  minorArcError := estimate.minorArcError
  majorArcLinearLowerBound := estimate.majorArcLinearLowerBound
  minorArcComplexContributionBound :=
    minorArcComplexContributionBound_of_dft_bound_sq_of_uniform_bound
      (majorArcs := estimate.majorArcs)
      (minorArcDftBound := estimate.minorArcDftBound)
      (minorArcError := estimate.minorArcError)
      estimate.minorArcDftBoundValid
      estimate.minorArcDftBoundSqErrorBound

noncomputable def
    VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound.canonicalContaminationThreshold
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound) :
    Nat :=
  estimate.toFourierComplexPositiveLinearCanonicalLowerBound.canonicalContaminationThreshold

noncomputable def
    VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toFourierComplexPositiveLinearCanonicalLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toFourierComplexPositiveLinearCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    hmajor hminor
    (by
      simpa
        [VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound.canonicalContaminationThreshold]
        using hcontamination)

theorem
    count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_positive_linear_canonical_lower_bound
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_complex_positive_linear_canonical_lower_bound
    estimate.toFourierComplexPositiveLinearCanonicalLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_dft_uniform_minor_sq_positive_linear_canonical_lower_bound
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_positive_linear_canonical_lower_bound
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_positive_linear_canonical_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_complex_positive_linear_canonical_lower_bound_le
    finite
    estimate.toFourierComplexPositiveLinearCanonicalLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_dft_uniform_minor_sq_positive_linear_canonical_lower_bound_le100
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_positive_linear_canonical_lower_bound_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  contaminationThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcError : Nat → ℝ
  majorArcLinearLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcContributionBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      |rawVonMangoldtFourierMinorArcContribution majorArcs n| ≤
        minorArcError n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        coefficient * (n : ℝ)

def
    VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound.rawThreshold
    (estimate :
      VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound) :
    Nat :=
  max estimate.majorArcThreshold estimate.minorArcThreshold

theorem
    VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound.majorArcThreshold_le_rawThreshold
    (estimate :
      VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound) :
    estimate.majorArcThreshold ≤ estimate.rawThreshold := by
  dsimp
    [VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound.rawThreshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound.minorArcThreshold_le_rawThreshold
    (estimate :
      VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound) :
    estimate.minorArcThreshold ≤ estimate.rawThreshold := by
  dsimp
    [VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound.rawThreshold]
  exact Nat.le_max_right _ _

noncomputable def
    VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound
    (estimate :
      VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound) :
    VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound where
  rawThreshold := estimate.rawThreshold
  contaminationThreshold := estimate.contaminationThreshold
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  rawLinearLowerBound := by
    intro n hn hEven
    have hmajorThreshold : estimate.majorArcThreshold < n :=
      lt_of_le_of_lt estimate.majorArcThreshold_le_rawThreshold hn
    have hminorThreshold : estimate.minorArcThreshold < n :=
      lt_of_le_of_lt estimate.minorArcThreshold_le_rawThreshold hn
    have hmajor :=
      estimate.majorArcLinearLowerBound n hmajorThreshold hEven
    have hminorAbs :=
      estimate.minorArcContributionBound n hminorThreshold hEven
    have hminorLower :
        -estimate.minorArcError n ≤
          rawVonMangoldtFourierMinorArcContribution estimate.majorArcs n :=
      (abs_le.mp hminorAbs).1
    rw [rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor
      estimate.majorArcs n]
    linarith
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.directRawWeightSumThreshold_le_of_components
    estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound
    (max_le hmajor hminor)
    hcontamination

theorem
    count_positive_above_of_vonMangoldt_fourier_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound
    estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_fourier_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_positive_linear_explicit_contamination_canonical_lower_bound
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_fourier_positive_linear_explicit_contamination_canonical_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound_le
    finite
    estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_fourier_positive_linear_explicit_contamination_canonical_lower_bound_le100
    (estimate :
      VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_positive_linear_explicit_contamination_canonical_lower_bound_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  contaminationThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcError : Nat → ℝ
  majorArcLinearLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcComplexContributionBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        coefficient * (n : ℝ)

noncomputable def
    VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound.toFourierPositiveLinearExplicitContaminationCanonicalLowerBound
    (estimate :
      VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound) :
    VonMangoldtFourierPositiveLinearExplicitContaminationCanonicalLowerBound where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  contaminationThreshold := estimate.contaminationThreshold
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  majorArcs := estimate.majorArcs
  minorArcError := estimate.minorArcError
  majorArcLinearLowerBound := estimate.majorArcLinearLowerBound
  minorArcContributionBound := by
    intro n hn hEven
    exact
      (real_abs_re_le_complex_norm
        (rawVonMangoldtFourierMinorArcComplexContribution
          estimate.majorArcs n)).trans
        (estimate.minorArcComplexContributionBound n hn hEven)
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toFourierPositiveLinearExplicitContaminationCanonicalLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toFourierPositiveLinearExplicitContaminationCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    hmajor hminor hcontamination

theorem
    count_positive_above_of_vonMangoldt_fourier_complex_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_positive_linear_explicit_contamination_canonical_lower_bound
    estimate.toFourierPositiveLinearExplicitContaminationCanonicalLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_fourier_complex_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_complex_positive_linear_explicit_contamination_canonical_lower_bound
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_fourier_complex_positive_linear_explicit_contamination_canonical_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_positive_linear_explicit_contamination_canonical_lower_bound_le
    finite
    estimate.toFourierPositiveLinearExplicitContaminationCanonicalLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_fourier_complex_positive_linear_explicit_contamination_canonical_lower_bound_le100
    (estimate :
      VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_complex_positive_linear_explicit_contamination_canonical_lower_bound_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  contaminationThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcDftBound : Nat → ℝ
  minorArcError : Nat → ℝ
  majorArcLinearLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcDftBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n
  minorArcDftBoundSqErrorBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      minorArcDftBound n ^ 2 ≤ minorArcError n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        coefficient * (n : ℝ)

noncomputable def
    VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound.toFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound) :
    VonMangoldtFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  contaminationThreshold := estimate.contaminationThreshold
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  majorArcs := estimate.majorArcs
  minorArcError := estimate.minorArcError
  majorArcLinearLowerBound := estimate.majorArcLinearLowerBound
  minorArcComplexContributionBound :=
    minorArcComplexContributionBound_of_dft_bound_sq_of_uniform_bound
      (majorArcs := estimate.majorArcs)
      (minorArcDftBound := estimate.minorArcDftBound)
      (minorArcError := estimate.minorArcError)
      estimate.minorArcDftBoundValid
      estimate.minorArcDftBoundSqErrorBound
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    hmajor hminor hcontamination

theorem
    count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_complex_positive_linear_explicit_contamination_canonical_lower_bound
    estimate.toFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_complex_positive_linear_explicit_contamination_canonical_lower_bound_le
    finite
    estimate.toFourierComplexPositiveLinearExplicitContaminationCanonicalLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound_le100
    (estimate :
      VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  contaminationThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcDftBound : Nat → ℝ
  majorArcLinearLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      coefficient * (n : ℝ) + minorArcDftBound n ^ 2 ≤
        rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcDftBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        coefficient * (n : ℝ)

noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound.toDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound) :
    VonMangoldtDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  contaminationThreshold := estimate.contaminationThreshold
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  majorArcs := estimate.majorArcs
  minorArcDftBound := estimate.minorArcDftBound
  minorArcError := fun n => estimate.minorArcDftBound n ^ 2
  majorArcLinearLowerBound := estimate.majorArcLinearLowerBound
  minorArcDftBoundValid := estimate.minorArcDftBoundValid
  minorArcDftBoundSqErrorBound := by
    intro n _hn _hEven
    rfl
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound.directRawWeightSumThreshold_le_of_components
    hmajor hminor hcontamination

theorem
    count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound
    estimate.toDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_positive_linear_explicit_contamination_canonical_lower_bound_le
    finite
    estimate.toDftUniformMinorSqPositiveLinearExplicitContaminationCanonicalLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound_le100
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorPositiveLinearExplicitContaminationCanonicalLowerBound)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_positive_linear_explicit_contamination_canonical_lower_bound_le
    goldbachUpTo100
    estimate
    hthreshold

theorem rawVonMangoldtFourierMinorArcContribution_lower_bound_of_complex_bound
    {minorArcThreshold : Nat}
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    {minorArcError : Nat → ℝ}
    (hminor :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
          minorArcError n) :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      -minorArcError n ≤
        rawVonMangoldtFourierMinorArcContribution majorArcs n := by
  intro n hn hEven
  have habs :
      |rawVonMangoldtFourierMinorArcContribution majorArcs n| ≤
        minorArcError n :=
    (real_abs_re_le_complex_norm
      (rawVonMangoldtFourierMinorArcComplexContribution majorArcs n)).trans
      (hminor n hn hEven)
  exact (abs_le.mp habs).1

structure
    VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  contaminationThreshold : Nat
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcError : Nat → ℝ
  majorArcLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      (1 - relativeError) *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +
        minorArcError n ≤
          rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcComplexContributionBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ‖rawVonMangoldtFourierMinorArcComplexContribution majorArcs n‖ ≤
        minorArcError n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ)

noncomputable def
    VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  decompositionThreshold := 0
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  contaminationThreshold := estimate.contaminationThreshold
  relativeError := estimate.relativeError
  relativeError_lt_one := estimate.relativeError_lt_one
  majorArcContribution :=
    rawVonMangoldtFourierMajorArcContribution estimate.majorArcs
  minorArcContribution :=
    rawVonMangoldtFourierMinorArcContribution estimate.majorArcs
  minorArcError := estimate.minorArcError
  rawDecomposition := by
    intro n _hn _hEven
    exact rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor
      estimate.majorArcs n
  majorArcLowerBound := estimate.majorArcLowerBound
  minorArcContributionLowerBound :=
    rawVonMangoldtFourierMinorArcContribution_lower_bound_of_complex_bound
      estimate.majorArcs
      estimate.minorArcComplexContributionBound
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    (Nat.zero_le B) hmajor hminor hcontamination

theorem
    count_positive_above_of_vonMangoldt_fourier_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate.toQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_fourier_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_fourier_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    finite
    estimate.toQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_fourier_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  contaminationThreshold : Nat
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcDftBound : Nat → ℝ
  minorArcError : Nat → ℝ
  majorArcLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      (1 - relativeError) *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +
        minorArcError n ≤
          rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcDftBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n
  minorArcDftBoundSqErrorBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      minorArcDftBound n ^ 2 ≤ minorArcError n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ)

noncomputable def
    VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  contaminationThreshold := estimate.contaminationThreshold
  relativeError := estimate.relativeError
  relativeError_lt_one := estimate.relativeError_lt_one
  majorArcs := estimate.majorArcs
  minorArcError := estimate.minorArcError
  majorArcLowerBound := estimate.majorArcLowerBound
  minorArcComplexContributionBound :=
    minorArcComplexContributionBound_of_dft_bound_sq_of_uniform_bound
      (majorArcs := estimate.majorArcs)
      (minorArcDftBound := estimate.minorArcDftBound)
      (minorArcError := estimate.minorArcError)
      estimate.minorArcDftBoundValid
      estimate.minorArcDftBoundSqErrorBound
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    hmajor hminor hcontamination

theorem
    count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_fourier_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate.toFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_dft_uniform_minor_sq_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_fourier_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    finite
    estimate.toFourierQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_dft_uniform_minor_sq_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  contaminationThreshold : Nat
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcDftBound : Nat → ℝ
  majorArcLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      (1 - relativeError) *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +
        minorArcDftBound n ^ 2 ≤
          rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcDftBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ)

noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  contaminationThreshold := estimate.contaminationThreshold
  relativeError := estimate.relativeError
  relativeError_lt_one := estimate.relativeError_lt_one
  majorArcs := estimate.majorArcs
  minorArcDftBound := estimate.minorArcDftBound
  minorArcError := fun n => estimate.minorArcDftBound n ^ 2
  majorArcLowerBound := estimate.majorArcLowerBound
  minorArcDftBoundValid := estimate.minorArcDftBoundValid
  minorArcDftBoundSqErrorBound := by
    intro n _hn _hEven
    rfl
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    hmajor hminor hcontamination

theorem
    count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate.toDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    finite
    estimate.toDftUniformMinorSqQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcDftBound : Nat → ℝ
  majorArcLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      (1 - relativeError) *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +
        minorArcDftBound n ^ 2 ≤
          rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcDftBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n

noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate) :
    Nat :=
  canonicalHLContaminationThreshold (1 / 4 : ℝ) estimate.relativeError
    (by norm_num) estimate.relativeError_lt_one

noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate.toFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate) :
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  contaminationThreshold := estimate.canonicalContaminationThreshold
  relativeError := estimate.relativeError
  relativeError_lt_one := estimate.relativeError_lt_one
  majorArcs := estimate.majorArcs
  minorArcDftBound := estimate.minorArcDftBound
  majorArcLowerBound := estimate.majorArcLowerBound
  minorArcDftBoundValid := estimate.minorArcDftBoundValid
  contaminationDominated := by
    intro n htn _hEven
    exact canonicalHLContaminationThreshold_spec
      (coefficient := (1 / 4 : ℝ))
      (relativeError := estimate.relativeError)
      (by norm_num)
      estimate.relativeError_lt_one
      n
      (le_of_lt htn)

noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    hmajor hminor hcontamination

theorem
    count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_canonical_contamination_weight_sum_estimate
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate.toFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_canonical_contamination_weight_sum_estimate
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_canonical_contamination_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_canonical_contamination_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    finite
    estimate.toFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_canonical_contamination_weight_sum_estimate_le100
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundCanonicalContaminationWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_canonical_contamination_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate where
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  contaminationThreshold : Nat
  contaminationThreshold_ge_two : 2 ≤ contaminationThreshold
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  majorArcs : (n : Nat) → Finset (ZMod n.succ)
  minorArcDftBound : Nat → ℝ
  majorArcLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      (1 - relativeError) *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +
        minorArcDftBound n ^ 2 ≤
          rawVonMangoldtFourierMajorArcContribution majorArcs n
  minorArcDftBoundValid :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      ∀ k ∈ zmodMinorFrequencies (majorArcs n),
        ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n
  contaminationSqrtLogModelBound :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ)

noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate.toFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate) :
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  contaminationThreshold := estimate.contaminationThreshold
  relativeError := estimate.relativeError
  relativeError_lt_one := estimate.relativeError_lt_one
  majorArcs := estimate.majorArcs
  minorArcDftBound := estimate.minorArcDftBound
  majorArcLowerBound := estimate.majorArcLowerBound
  minorArcDftBoundValid := estimate.minorArcDftBoundValid
  contaminationDominated :=
    quarter_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_dominated_of_sqrt_log_model_ge_two_threshold
      estimate.contaminationThreshold_ge_two
      estimate.contaminationSqrtLogModelBound

noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    hmajor hminor hcontamination

theorem
    count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate.toFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    finite
    estimate.toFixedErrorQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_dft_uniform_minor_sq_fixed_error_quarter_major_minor_lower_bound_sqrt_log_contamination_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

/-! Trivial-decomposition lemmas.  When the major arc set is `Finset.univ`, the
minor frequency set is empty and the major arc Fourier contribution equals the
raw von Mangoldt convolution itself.  This turns the DFT-level circle method
into a sound packaging of any raw positive-linear lower bound. -/

theorem zmodMinorFrequencies_univ {N : Nat} [NeZero N] :
    zmodMinorFrequencies (Finset.univ : Finset (ZMod N)) = ∅ := by
  ext k
  simp [zmodMinorFrequencies]

theorem rawVonMangoldtFourierMinorArcComplexContribution_univ
    (n : Nat) :
    rawVonMangoldtFourierMinorArcComplexContribution
        (fun n : Nat => (Finset.univ : Finset (ZMod n.succ))) n = 0 := by
  simp [rawVonMangoldtFourierMinorArcComplexContribution,
    zmodMinorArcContribution]

theorem rawVonMangoldtFourierMinorArcContribution_univ
    (n : Nat) :
    rawVonMangoldtFourierMinorArcContribution
        (fun n : Nat => (Finset.univ : Finset (ZMod n.succ))) n = 0 := by
  simp [rawVonMangoldtFourierMinorArcContribution,
    rawVonMangoldtFourierMinorArcComplexContribution_univ]

theorem rawVonMangoldtFourierMajorArcContribution_univ
    (n : Nat) :
    rawVonMangoldtFourierMajorArcContribution
        (fun n : Nat => (Finset.univ : Finset (ZMod n.succ))) n =
      RawVonMangoldtGoldbachSum n := by
  have h := rawVonMangoldtGoldbachSum_eq_fourier_major_add_minor
    (majorArcs := fun n : Nat => (Finset.univ : Finset (ZMod n.succ))) n
  have hminor := rawVonMangoldtFourierMinorArcContribution_univ n
  linarith [h, hminor]

/-! Auto-contamination constructor: builds the sqrt-log contamination estimate
from just the major/minor arc obligations.  The contamination threshold is
extracted from the asymptotic `K * sqrt(n) * log(n)^3 = o(n)` lemma via
`Classical.choose`, so the analytic side never has to certify the contamination
inequality directly.  This is purely a packaging convenience — it does not
provide either the major arc lower bound or the minor arc DFT bound. -/
noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate.ofMajorMinorObligations
    {relativeError : ℝ} (hrelativeError : relativeError < 1)
    (majorArcThreshold minorArcThreshold : Nat)
    (majorArcs : (n : Nat) → Finset (ZMod n.succ))
    (minorArcDftBound : Nat → ℝ)
    (majorArcLowerBound :
      ∀ n : Nat, majorArcThreshold < n → Even n →
        (1 - relativeError) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +
          minorArcDftBound n ^ 2 ≤
            rawVonMangoldtFourierMajorArcContribution majorArcs n)
    (minorArcDftBoundValid :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        ∀ k ∈ zmodMinorFrequencies (majorArcs n),
          ‖vonMangoldtZModDft n k‖ ≤ minorArcDftBound n) :
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate where
  majorArcThreshold := majorArcThreshold
  minorArcThreshold := minorArcThreshold
  contaminationThreshold :=
    canonicalQuarterSqrtLogModelThreshold relativeError hrelativeError
  contaminationThreshold_ge_two :=
    canonicalQuarterSqrtLogModelThreshold_ge_two hrelativeError
  relativeError := relativeError
  relativeError_lt_one := hrelativeError
  majorArcs := majorArcs
  minorArcDftBound := minorArcDftBound
  majorArcLowerBound := majorArcLowerBound
  minorArcDftBoundValid := minorArcDftBoundValid
  contaminationSqrtLogModelBound :=
    canonicalQuarterSqrtLogModelThreshold_spec hrelativeError

/-! Trivial-major-arc constructor.  Genius move: take the major arc set to be
all of `ZMod (n+1)`.  Then the minor frequency set is empty, the minor arc DFT
bound is vacuous, and the major arc Fourier contribution equals
`RawVonMangoldtGoldbachSum n` exactly.  This means a direct raw von Mangoldt
positive-linear lower bound is enough to populate the entire DFT major/minor
sqrt-log contamination estimate.  Both the minor arc obligation and the
contamination model bound are discharged inside Lean. -/
noncomputable def
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate.ofRawQuarterLowerBound
    (rawThreshold : Nat)
    {relativeError : ℝ} (hrelativeError : relativeError < 1)
    (rawLowerBound :
      ∀ n : Nat, rawThreshold < n → Even n →
        (1 - relativeError) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
          RawVonMangoldtGoldbachSum n) :
    VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate :=
  VonMangoldtDftUniformMinorSqFixedErrorQuarterMajorMinorLowerBoundSqrtLogContaminationCanonicalWeightSumEstimate.ofMajorMinorObligations
    (hrelativeError := hrelativeError)
    (majorArcThreshold := rawThreshold)
    (minorArcThreshold := rawThreshold)
    (majorArcs := fun n : Nat => (Finset.univ : Finset (ZMod n.succ)))
    (minorArcDftBound := fun _ : Nat => (0 : ℝ))
    (majorArcLowerBound := by
      intro n htn hEven
      have hraw := rawLowerBound n htn hEven
      have hmaj := rawVonMangoldtFourierMajorArcContribution_univ n
      have hzero : (0 : ℝ) ^ (2 : Nat) = 0 := by norm_num
      have : (1 - relativeError) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +
          (0 : ℝ) ^ (2 : Nat) ≤
            RawVonMangoldtGoldbachSum n := by
        rw [hzero]
        linarith
      simpa [hmaj] using this)
    (minorArcDftBoundValid := by
      intro n _ _ k hk
      rw [zmodMinorFrequencies_univ] at hk
      simp at hk)

end DiscreteCircleMethod
end Gdbh
