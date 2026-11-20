import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerNormalFormBlockUnitriangular
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Amp.StabNormal.stabiliser_normal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCommonStabilizerNormalFormBlockUnitriangular.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular : ∀ (k r : ℕ) (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ → Rset k r g₀ = Set.range (fun x : UTin β → ℂ => uEmb k r (upperIn β x)) ∧ IsClosedSub k r (Rset k r g₀) ∧ IsHaarOn (Rset k r g₀) (lebR k r β) ∧ IsUnimod (Rset k r g₀) (lebR k r β) ∧ IsNormal k r β g₀⁻¹ ∧ (lebR k r β).map (conjM g₀) = lebR k r β := by
  first | exact @GlobalTheory.Amp.StabNormal.stabiliser_normal | exact GlobalTheory.Amp.StabNormal.stabiliser_normal | (intros; apply GlobalTheory.Amp.StabNormal.stabiliser_normal <;> assumption)
