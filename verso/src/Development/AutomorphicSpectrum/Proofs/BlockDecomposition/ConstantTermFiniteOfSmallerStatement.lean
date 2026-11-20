import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FConstantTermFiniteOfSmaller.lean&line=196#L196)
-/
theorem _root_.GlobalTheory.T.constant_term_finite_of_smaller : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) → ∀ r, 0 < r → r < a → CTFin E a r := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.ctFin | exact GlobalTheory.CompanionTheory.CTFin.ctFin | (intros; apply GlobalTheory.CompanionTheory.CTFin.ctFin <;> assumption)
