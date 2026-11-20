import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenGoodOfAdmissibilityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigCLe
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EigGoodTypes.main_alt_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FEigCLe.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.eigGood_of_archimedean_signature_adm5 : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → Formalism.MainNotions.SumRepresentations.tieLab D → MtParTie D.nd D.naut D.ntypes → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → GlobalTheory.NRows.GoodIdempotentFixesLocalisationForms D → GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector X → ∀ i, GlobalTheory.NJoin.EigGood X i := by
  first | exact @_root_.GlobalTheory.EigGoodTypes.main_alt_alt | exact _root_.GlobalTheory.EigGoodTypes.main_alt_alt | (intros; apply _root_.GlobalTheory.EigGoodTypes.main_alt_alt <;> assumption)
end
