import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitarySignatureStabiliserCosetCutoff
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsUnitarySignatureStabiliserCosetCutoff.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.exists_unitarySignatureStabiliserCosetCutoff : ∀ (c : CDHaar) (P Q P' Q' : ℕ) (x₀ : ActionCoordinates.Wsp P Q), ActionCoordinates.qf x₀ ≠ 0 → ∀ (j : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q) (ι : UpqT P' Q' → UpqT P Q), ActionCoordinates.IsPerpFrame x₀ j ι → Set.range ι = {g | ActionCoordinates.act g x₀ = x₀} → ∃ u : UpqT P Q → ℝ≥0∞, Measurable u ∧ ∀ g, Measurable (fun h => u (ι h * g)) ∧ ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1 := by
  first | exact @GlobalTheory.StabiliserCutoff.exists_cutoff | exact GlobalTheory.StabiliserCutoff.exists_cutoff | (intros; apply GlobalTheory.StabiliserCutoff.exists_cutoff <;> assumption)
