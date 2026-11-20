import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafLevelSquareBound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OnWithOfIsEmpty
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.levelSq_yBound_atRec` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeafLevelSquareBound.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.leaf_level_square_bound : AtRec fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  first | exact @GlobalTheory.BigOn.levelSq_yBound_atRec | exact GlobalTheory.BigOn.levelSq_yBound_atRec | (intros; apply GlobalTheory.BigOn.levelSq_yBound_atRec <;> assumption)
