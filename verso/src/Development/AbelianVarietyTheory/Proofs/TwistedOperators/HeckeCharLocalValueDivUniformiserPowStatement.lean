import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharLocalValueDivUniformiserPow
import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
open NumberField IsDedekindDomain Formalism.L2.Host
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHeckeCharLocalValueDivUniformiserPow.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.heckeChar_local_value_div_uniformiser_pow : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), ∃ N : ℕ, 0 < N ∧ ∀ (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ), ∃ a : ℤ, ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) ^ N = 1 := by
  first | exact @GlobalTheory.HeckeLocDec.loc_div_val_pow | exact GlobalTheory.HeckeLocDec.loc_div_val_pow | (intros; apply GlobalTheory.HeckeLocDec.loc_div_val_pow <;> assumption)
