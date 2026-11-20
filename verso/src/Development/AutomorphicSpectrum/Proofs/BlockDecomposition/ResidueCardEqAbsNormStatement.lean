import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueCardEqAbsNorm
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FResidueCardEqAbsNorm.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.residue_card_eq_abs_norm : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (resCard (w.adicCompletion E) : ℝ) = (Ideal.absNorm w.asIdeal : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm | exact GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm | (intros; apply GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm <;> assumption)
