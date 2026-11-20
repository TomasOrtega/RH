import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuationAlgebraMapEqOfInertPlace.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.valuation_algebraMap_eq_of_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ x : F, w.valuation E (algebraMap F E x) = v.valuation F x := by
  first | exact @GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt | exact GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt | (intros; apply GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt <;> assumption)
