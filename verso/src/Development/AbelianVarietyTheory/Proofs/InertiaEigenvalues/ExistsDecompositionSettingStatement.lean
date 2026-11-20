import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionSetting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsDecompositionSetting.lean&line=145#L145)
-/
theorem _root_.GlobalTheory.T.exists_decomposition_setting : GlobalTheory.TwSys.Cheb → ∀ (D : D7), SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc, ZDecomp D.nd i → Live D.nd i → ∃ (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i rep ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting D.R.t (D.nd.T i) (D.nd.Z i) rep ρ (D.nd.chi i) := by
  first | exact @GlobalTheory.AbsoluteIrreducibilityOfTraceSpan.setting_of_live | exact GlobalTheory.AbsoluteIrreducibilityOfTraceSpan.setting_of_live | (intros; apply GlobalTheory.AbsoluteIrreducibilityOfTraceSpan.setting_of_live <;> assumption)
