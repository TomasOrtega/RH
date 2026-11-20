import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternSetCardColumnStep
import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPatternSetCardColumnStep.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.pattern_set_card_column_step : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j < d →
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe | exact GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe <;> assumption)
