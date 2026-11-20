import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSelfDualMeasureExistsUniqueFourierInversion.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → (∃! μ : Measure V, SelfDual μ (fun x y => ψ (β x y))) ∧ ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ f, IsTest f → IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  first | exact @GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest | exact GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest | (intros; apply GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest <;> assumption)
