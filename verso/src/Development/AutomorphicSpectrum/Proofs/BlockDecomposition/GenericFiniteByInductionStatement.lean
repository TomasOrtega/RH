import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGenericFiniteByInduction.lean&line=229#L229)
-/
theorem _root_.GlobalTheory.T.generic_finite_by_induction : (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), CuspFin E a) → (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) → ∀ r, 0 < r → r < a → CTFin E a r) → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GenFin E a := by
  first | exact @GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters | exact GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters | (intros; apply GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters <;> assumption)
