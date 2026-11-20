import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalZeroOfInjectivePower
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFunctionalZeroOfInjectivePower.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.functional_zero_of_injective_power : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (A : V →ₗ[ℂ] V), Function.Injective A → ∀ (l : V →ₗ[ℂ] ℂ) (v : V) (j₀ : ℕ), (∀ j ≥ j₀, l ((A ^ j) v) = 0) → l v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates | exact GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates | (intros; apply GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates <;> assumption)
