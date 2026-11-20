import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[mul_sub, mul_one, ← mul_assoc, map_sub]`. Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ n`.

Rewrite using `[PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]`. Simplify using `[PowerSeries.coeff_one, pow_succ]`.
-/
private theorem UpperTheory.geometric_power_series_inverse (x : ℂ) :
    (PowerSeries.mk fun k : ℕ => x ^ k) * (1 - PowerSeries.C x * PowerSeries.X) = 1 := by
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  cases n with
  | zero => simp
  | succ n =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
    simp [PowerSeries.coeff_one, pow_succ]

/- English proof (translation)
Introduce `x y`. Establish `h : (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i))) = (PowerSeries.mk fun k : ℕ => x ^ k) * (PowerSeries.mk fun k : ℕ => y ^ k)`. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Simplify using the standard rewrite rules.

Rewrite using `[h, mul_mul_mul_comm, UpperTheory.geometric_power_series_inverse, UpperTheory.geometric_power_series_inverse, mul_one]`.
-/
theorem UpperTheory.powerSeries_completeHomogeneous_two_mul_eq_one :
    ∀ x y : ℂ, (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i))) * ((1 - PowerSeries.C x * PowerSeries.X) * (1 - PowerSeries.C y * PowerSeries.X)) = 1 := by
  intro x y
  have h : (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i)))
      = (PowerSeries.mk fun k : ℕ => x ^ k) * (PowerSeries.mk fun k : ℕ => y ^ k) := by
    ext n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp
  rw [h, mul_mul_mul_comm, UpperTheory.geometric_power_series_inverse, UpperTheory.geometric_power_series_inverse, mul_one]
