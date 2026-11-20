import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Rodier.whitHeredity` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerHeredity.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.whittaker_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.whitHeredity | exact GlobalTheory.CompanionTheory.Rodier.whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Rodier.whitHeredity <;> assumption)
