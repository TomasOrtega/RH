import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBumpWithNonzeroIntegral
import Mathlib
open MeasureTheory
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsBumpWithNonzeroIntegral.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_bump_with_nonzero_integral : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) (U : Set X), IsOpen U → m Uᶜ = 0 → m ≠ 0 → (∀ χ : X → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ U → Integrable χ m) → ∃ χ : X → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∫ x, χ x ∂m ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MeasureBump.exists_integral_ne_zero_of_carried_by_isOpen | exact GlobalTheory.CompanionTheory.MeasureBump.exists_integral_ne_zero_of_carried_by_isOpen | (intros; apply GlobalTheory.CompanionTheory.MeasureBump.exists_integral_ne_zero_of_carried_by_isOpen <;> assumption)
