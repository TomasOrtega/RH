import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModuleAdicComplete
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteModuleAdicComplete.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finite_module_adic_complete : ∀ (O M : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [AddCommGroup M] [Module O M] [Module.Finite O M], IsAdicComplete (IsLocalRing.maximalIdeal O) M := by
  first | exact @GlobalTheory.CompanionTheory.FiniteComplete.isAdicComplete_of_finite | exact GlobalTheory.CompanionTheory.FiniteComplete.isAdicComplete_of_finite | (intros; apply GlobalTheory.CompanionTheory.FiniteComplete.isAdicComplete_of_finite <;> assumption)
