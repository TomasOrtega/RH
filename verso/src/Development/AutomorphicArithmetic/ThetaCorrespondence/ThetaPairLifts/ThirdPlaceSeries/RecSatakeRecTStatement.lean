import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatakeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSatakeRecT
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod_and_speh_and_satake` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FRecSatakeRecT.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.recProd_recSpeh_recSatake : GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  first | exact @_root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod_and_speh_and_satake | exact _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod_and_speh_and_satake | (intros; apply _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod_and_speh_and_satake <;> assumption)
end
