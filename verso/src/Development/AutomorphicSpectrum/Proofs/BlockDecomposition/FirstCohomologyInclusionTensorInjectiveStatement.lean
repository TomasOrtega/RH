import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyInclusionTensorInjective
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFirstCohomologyInclusionTensorInjective.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.first_cohomology_inclusion_tensor_injective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), H1CommutesBaseChange F → ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective ((iotaQ F).lTensor M) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective | exact GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective <;> assumption)
