import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private def UpperTheory.powerSeriesFirstDifferenceSeq (a : ℂ) (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => f 0
  | k + 1 => f (k + 1) - a * f k

/- English proof (translation)
Establish `h : PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) = PowerSeries.mk f - PowerSeries.C a * (PowerSeries.mk f * PowerSeries.X)` using `by ring`. Rewrite using `[h]`. Use extensionality with `k`. Consider the cases of `k with`. Consider the case `zero => simp [UpperTheory.powerSeriesFirstDifferenceSeq]`.

Consider the case `succ k`. Rewrite using `[map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X]`. Simplify using `[UpperTheory.powerSeriesFirstDifferenceSeq]`.
-/
private theorem UpperTheory.power_series_mul_linear (a : ℂ) (f : ℕ → ℂ) :
    PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.mk (UpperTheory.powerSeriesFirstDifferenceSeq a f) := by
  have h : PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.mk f - PowerSeries.C a * (PowerSeries.mk f * PowerSeries.X) := by ring
  rw [h]
  ext k
  cases k with
  | zero => simp [UpperTheory.powerSeriesFirstDifferenceSeq]
  | succ k =>
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X]
    simp [UpperTheory.powerSeriesFirstDifferenceSeq]

/- English proof (translation)
Rewrite using `[Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one, add_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ k` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Rewrite using `[Nat.succ_sub hi', pow_succ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem UpperTheory.geometric_sum_recurrence (x y : ℂ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1 + 1), x ^ i * y ^ (k + 1 - i)) =
      x ^ (k + 1) + y * ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.succ_sub hi', pow_succ]
  ring

/- English proof (translation)
Rewrite using `[← mul_assoc, ← mul_assoc, ← mul_assoc, UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear]`. Establish `hS2 : ∀ k, S (k + 1 + 1) = (x + y) * S (k + 1) - x * y * S k` using `fun k => by`. Rewrite using `[hS (k + 1), hS k]`. Expand and normalize the polynomial expressions, which then agree. Establish `hT2 : ∀ k, T (k + 1 + 1) = (x' + y') * T (k + 1) - x' * y' * T k` using `fun k => by`.

Rewrite using `[hT (k + 1), hT k]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `k`. Rewrite using `[map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_one, PowerSeries.coeff_mk]`. Break down `k with _ | _ | _ | _ | k` into its components or cases.

Simplify using `[UpperTheory.powerSeriesFirstDifferenceSeq, hS0, hT0]`. Simplify using `only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]`.

Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Simplify using `only [UpperTheory.powerSeriesFirstDifferenceSeq, hS2, hT2]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem UpperTheory.product_four_geometric_series (x y x' y' c : ℂ) (S T : ℕ → ℂ)
    (hS0 : S 0 = 1) (hT0 : T 0 = 1)
    (hS : ∀ k, S (k + 1) = x ^ (k + 1) + y * S k)
    (hT : ∀ k, T (k + 1) = x' ^ (k + 1) + y' * T k) :
    (PowerSeries.mk fun k : ℕ => c ^ k * S k * T k) *
          ((1 - PowerSeries.C (x * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (x * y' * c) * PowerSeries.X) *
            (1 - PowerSeries.C (y * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (y * y' * c) * PowerSeries.X)) =
          1 - PowerSeries.C (x * y * x' * y' * c ^ 2) * PowerSeries.X ^ 2 := by
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear,
    UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear]
  have hS2 : ∀ k, S (k + 1 + 1) = (x + y) * S (k + 1) - x * y * S k := fun k => by
    rw [hS (k + 1), hS k]; ring
  have hT2 : ∀ k, T (k + 1 + 1) = (x' + y') * T (k + 1) - x' * y' * T k := fun k => by
    rw [hT (k + 1), hT k]; ring
  ext k
  rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_one,
    PowerSeries.coeff_mk]
  rcases k with _ | _ | _ | _ | k
  · simp [UpperTheory.powerSeriesFirstDifferenceSeq, hS0, hT0]
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · rw [if_neg (by omega), if_neg (by omega)]
    simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS2, hT2]
    ring

/- English proof (translation)
Introduce `x y x' y' c`. Conclude with `UpperTheory.product_four_geometric_series x y x' y' c (fun k => ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i)) (fun k => ∑ i ∈ Finset.range (k + 1), x' ^ i * y' ^ (k - i)) (by simp) (by simp) (UpperTheory.geometric_sum_recurrence x y) (UpperTheory.geometric_sum_recurrence x' y' …`.
-/
theorem UpperTheory.rankinSelberg_local_generating_series_identity :
    ∀ x y x' y' c : ℂ, (PowerSeries.mk fun k : ℕ => c ^ k * (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i)) * (∑ i ∈ Finset.range (k + 1), (x') ^ i * (y') ^ (k - i))) *
          ((1 - PowerSeries.C (x * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (x * y' * c) * PowerSeries.X) *
            (1 - PowerSeries.C (y * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (y * y' * c) * PowerSeries.X)) =
          1 - PowerSeries.C (x * y * x' * y' * c ^ 2) * PowerSeries.X ^ 2 := by
  intro x y x' y' c
  exact UpperTheory.product_four_geometric_series x y x' y' c
    (fun k => ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i))
    (fun k => ∑ i ∈ Finset.range (k + 1), x' ^ i * y' ^ (k - i))
    (by simp) (by simp) (UpperTheory.geometric_sum_recurrence x y) (UpperTheory.geometric_sum_recurrence x' y')
