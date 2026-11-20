import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryGroupCountEqMainTerm
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DefiniteFiniteCount
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FDefiniteUnitaryGroupCountEqMainTerm.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.definiteUnitaryGroup_count_eq_mainTerm : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount.DefiniteHyp B d p → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → (B.D : ℝ) = mainTerm B d := by
  first | exact @GlobalTheory.Dec.definite_count_of_finite | exact GlobalTheory.Dec.definite_count_of_finite | (intros; apply GlobalTheory.Dec.definite_count_of_finite <;> assumption)
