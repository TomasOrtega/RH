import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierLinear
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.WeilMix.ptrB_linear` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMixedModelPartialFourierLinear.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.mixedModelPartialFourier_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_linear | exact GlobalTheory.JR.WeilMix.ptrB_linear | (intros; apply GlobalTheory.JR.WeilMix.ptrB_linear <;> assumption)
