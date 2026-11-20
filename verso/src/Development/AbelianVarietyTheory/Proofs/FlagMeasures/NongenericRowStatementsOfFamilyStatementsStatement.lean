import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NongenericRowStatementsOfFamilyStatements
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SnFamNG.leaves_of_fam` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FNongenericRowStatementsOfFamilyStatements.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.nongeneric_row_statements_of_family_statements : FamNG → (FamilyWeightSumUnfoldingIdentity → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) ∧ (WeightsFam → Formalism.L2.SG.FamDefs.WeightsNG) ∧ (FamilyGroupSumFactorsWeightAmplitude → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) ∧ (ExistFam → Formalism.L2.SG.FamDefs.ExistNG) := by
  first | exact @GlobalTheory.SnFamNG.leaves_of_fam | exact GlobalTheory.SnFamNG.leaves_of_fam | (intros; apply GlobalTheory.SnFamNG.leaves_of_fam <;> assumption)
