import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodCuspPoint.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FGoodLabelsRankPartParameterCuspidal.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.goodLabels_rank_part_parameter_cuspidal : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tieLab D → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut := by
  first | exact @GlobalTheory.GoodCuspPoint.main | exact GlobalTheory.GoodCuspPoint.main | (intros; apply GlobalTheory.GoodCuspPoint.main <;> assumption)
