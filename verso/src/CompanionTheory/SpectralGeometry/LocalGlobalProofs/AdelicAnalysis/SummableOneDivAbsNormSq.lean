import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import ReciprocityTheory.Chebotarev.EulerSum

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Primes

/- English proof (translation)
Introduce `F _ _`. Establish `h` using `(ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F (s := 2) (by norm_num)).comp_injective (i := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)`. Use `h.congr fun v => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[Real.rpow_neg (Nat.cast_nonneg _), one_div]`.

Evaluate the numerical expressions.
-/
theorem summable_one_div_absNorm_sq :
    ∀ (F : Type) [Field F] [NumberField F],
      Summable fun v : HeightOneSpectrum (𝓞 F) => 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro F _ _
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F (s := 2) (by norm_num)).comp_injective
    (i := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)
  refine h.congr fun v => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  norm_num

end GlobalTheory.CompanionTheory.SW.Primes
