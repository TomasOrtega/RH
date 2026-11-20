import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLangStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFuncStatement

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB

/- English proof (translation)
Introduce `k K _ _ _ _ _`. Conclude with `GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros (RatFunc k) K (GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt k)`.
-/
theorem tsen : Tsen := by
  intro k K _ _ _ _ _
  exact GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros (RatFunc k) K (GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt k)

end GlobalTheory.NeedB
