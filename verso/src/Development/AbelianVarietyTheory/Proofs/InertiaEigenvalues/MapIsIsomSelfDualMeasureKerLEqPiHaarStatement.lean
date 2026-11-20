import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapIsIsomSelfDualMeasureKerLEqPiHaar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMapIsIsomSelfDualMeasureKerLEqPiHaar.lean&line=174#L174)
-/
theorem _root_.GlobalTheory.T.map_isIsom_selfDualMeasure_kerL_eq_pi_haar : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → (∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) ∧ ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → (letI := M.mE; Measure.map j μ = Measure.pi fun _ : Fin r => M.μE) := by
  first | exact @GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi | exact GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi | (intros; apply GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi <;> assumption)
