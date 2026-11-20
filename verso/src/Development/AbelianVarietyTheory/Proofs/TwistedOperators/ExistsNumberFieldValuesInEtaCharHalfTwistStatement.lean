import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNumberFieldValuesInEtaCharHalfTwist
import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharHost
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
open NumberField IsDedekindDomain Formalism.L2.Host
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaValsNumberField.etaVals` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsNumberFieldValuesInEtaCharHalfTwist.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.exists_numberField_valuesIn_etaChar_halfTwist : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsEtaT H χ → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn (1 / 2) (algebraMap M ℂ) := by
  first | exact @GlobalTheory.EtaValsNumberField.etaVals | exact GlobalTheory.EtaValsNumberField.etaVals | (intros; apply GlobalTheory.EtaValsNumberField.etaVals <;> assumption)
