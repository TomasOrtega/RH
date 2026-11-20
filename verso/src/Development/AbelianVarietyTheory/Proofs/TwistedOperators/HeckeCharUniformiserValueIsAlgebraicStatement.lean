import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUniformiserValueIsAlgebraic
import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
open NumberField IsDedekindDomain Formalism.L2.Host
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.heckeChar_val_isAlgebraic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHeckeCharUniformiserValueIsAlgebraic.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.heckeChar_uniformiser_value_isAlgebraic : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ), (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) → ∀ w : HeightOneSpectrum (𝓞 L), IsAlgebraic ℚ ((χ.val w : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.heckeChar_val_isAlgebraic | exact GlobalTheory.heckeChar_val_isAlgebraic | (intros; apply GlobalTheory.heckeChar_val_isAlgebraic <;> assumption)
