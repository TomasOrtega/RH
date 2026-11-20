import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealNormProductOverPlaces
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightSmulInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEvEqProdNormZpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain
open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdealNormProductOverPlaces.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.ideal_norm_product_over_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (I : FractionalIdeal (𝓞 E)⁰ E), I ≠ 0 →
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v,
        (Ideal.absNorm w.asIdeal : ℝ) ^ FractionalIdeal.count E w I = (FractionalIdeal.absNorm I : ℝ) := by
  first | exact @GlobalTheory.RegroupAbsNorm.finprod_aboveF_absNorm_zpow_count | exact GlobalTheory.RegroupAbsNorm.finprod_aboveF_absNorm_zpow_count | (intros; apply GlobalTheory.RegroupAbsNorm.finprod_aboveF_absNorm_zpow_count <;> assumption)
