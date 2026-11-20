import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleVectorHaarExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdeleVectorHaarExists.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.adele_vector_haar_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ),
    ∃ μ : @Measure (Fin d → AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ := by
  first | exact @GlobalTheory.AdelicHaarCoord.exists_addHaar_borel | exact GlobalTheory.AdelicHaarCoord.exists_addHaar_borel | (intros; apply GlobalTheory.AdelicHaarCoord.exists_addHaar_borel <;> assumption)
