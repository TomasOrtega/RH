import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergReproducingKernelSumSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeisenbergReproducingKernelSumSpec.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.heisenbergReproducingKernelSum_spec : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (α : V → ℂ), IsSemichar H Λ α → (∀ w z, Summable (fun x : Λ => α x * kerTerm H x w z)) ∧ (∀ z, Differentiable ℂ (kerSum H Λ α z)) ∧ ∀ z, ∀ y ∈ Λ, ∀ w, α y * Heisenberg₂ H y (kerSum H Λ α z) w = kerSum H Λ α z w := by
  first | exact @GlobalTheory.UnitaryTheta.KerSum.kerSum_spec | exact GlobalTheory.UnitaryTheta.KerSum.kerSum_spec | (intros; apply GlobalTheory.UnitaryTheta.KerSum.kerSum_spec <;> assumption)
