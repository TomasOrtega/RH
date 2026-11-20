import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableVtQT
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormRepGeneratorsAndThetaSeriesTerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ex.summable_vt_QT` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FSummableVtQT.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.summable_vt_of_int : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) := by
  first | exact @GlobalTheory.Ex.summable_vt_QT | exact GlobalTheory.Ex.summable_vt_QT | (intros; apply GlobalTheory.Ex.summable_vt_QT <;> assumption)
