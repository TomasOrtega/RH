import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

/- English proof (translation)
Introduce `F _ _ _ 𝔞 s`. Establish `hsq : (omegaFactor 𝔞 : ℝ) ^ 2 = (|(discr F : ℝ)| * ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) ^ 2)`. Simplify using `only [omegaFactor, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm, ← Real.sqrt_eq_rpow]`. Rewrite using `[mul_pow, Real.sq_sqrt (abs_nonneg _)]`. Establish `h2 : (omegaFactor 𝔞 : ℂ) ^ (2 * s) = (((omegaFactor 𝔞 : ℝ) ^ 2) ^ s : ℝ)` using `by push_cast; rw [pow_mul]`.

Rewrite using `[h2, hsq]`. Use `push_cast`. Rewrite using `[mul_pow, ← pow_mul]`. Use `congr 2`. Rewrite using `[← Complex.ofReal_ratCast, Rat.cast_abs, Rat.cast_intCast]`.
-/
theorem omegaFactor_pow_two_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 : Frac F) (s : ℕ), (omegaFactor 𝔞 : ℂ) ^ (2 * s) = ((|(discr F : ℚ)| ^ s * FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ^ (2 * s) : ℚ) : ℂ) := by
  intro F _ _ _ 𝔞 s
  have hsq : (omegaFactor 𝔞 : ℝ) ^ 2 = (|(discr F : ℝ)| * ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) ^ 2) := by
    simp only [omegaFactor, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm, ← Real.sqrt_eq_rpow]
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
  have h2 : (omegaFactor 𝔞 : ℂ) ^ (2 * s) = (((omegaFactor 𝔞 : ℝ) ^ 2) ^ s : ℝ) := by
    push_cast; rw [pow_mul]
  rw [h2, hsq]
  push_cast
  rw [mul_pow, ← pow_mul]
  congr 2
  rw [← Complex.ofReal_ratCast, Rat.cast_abs, Rat.cast_intCast]

end GlobalTheory.HilbFam
