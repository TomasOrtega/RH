import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdicIntegersCharacterDualIndexEqResidueCardZpow
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DualIndexPow.nIdx_eq_zpow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FAdicIntegersCharacterDualIndexEqResidueCardZpow.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.adicIntegersCharacterDualIndex_eq_residue_card_zpow : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (c : ℤ), (∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp c) → LocalAdditiveCharacterDual.nIdx F ψ v = (PlaceSplittingTypes.resCard F v : ℝ) ^ c := by
  first | exact @GlobalTheory.DualIndexPow.nIdx_eq_zpow | exact GlobalTheory.DualIndexPow.nIdx_eq_zpow | (intros; apply GlobalTheory.DualIndexPow.nIdx_eq_zpow <;> assumption)
