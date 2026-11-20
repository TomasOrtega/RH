import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFiniteAlgebraJacobsonRadical
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalFiniteAlgebraJacobsonRadical.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.local_finite_algebra_jacobson_radical : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Module.Finite O R], Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) ≤ (⊥ : Ideal R).jacobson ∧ ∃ N : ℕ, (⊥ : Ideal R).jacobson ^ N ≤ Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) := by
  first | exact @GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le | exact GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le | (intros; apply GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le <;> assumption)
