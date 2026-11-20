import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareVectorBundleRank
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExteriorSquareVectorBundleRank.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exterior_square_vector_bundle_rank : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (g : ℕ), VB R V g → VB R (⋀[R]^2 V) (g.choose 2) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two | exact GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two <;> assumption)
