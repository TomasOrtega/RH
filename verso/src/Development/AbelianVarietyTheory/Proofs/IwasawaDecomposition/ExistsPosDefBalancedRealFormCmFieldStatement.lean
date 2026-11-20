import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosDefBalancedRealFormCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsPosDefBalancedRealFormCmField.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.exists_posDef_balanced_realForm_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, B ∈ realForms H.bar X ∧ IsPosDef B := by
  first | exact @GlobalTheory.DefForm.exists_posDef_realForm | exact GlobalTheory.DefForm.exists_posDef_realForm | (intros; apply GlobalTheory.DefForm.exists_posDef_realForm <;> assumption)
