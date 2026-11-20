import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProduct
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerHeredityGenericProduct.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.whittaker_heredity_generic_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k → GenericProdIff k := by
  first | exact @GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | exact GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity <;> assumption)
