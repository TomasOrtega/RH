import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedInverseOfLiftLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftReductionZeroOfMaximalStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGeneralizedInverseOfLiftLocal.lean&line=145#L145)
-/
theorem _root_.GlobalTheory.T.generalized_inverse_of_lift_local : ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N), Lift b → ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift | exact GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift <;> assumption)
