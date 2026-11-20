import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.UnipotentAdelicQuotients.StdAdditiveCharExists
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.BridgeStdAddChar
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdelicChar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_isCharAF_of_std :
    HeckeCharacterZeroLocus.StdAdditiveCharExists → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F →
      ∃ ψ, IsCharAF F ψ := by
  intro h F _ _ hF
  obtain ⟨ψ, h1, h2, h3, h4, -⟩ := h F hF
  exact ⟨ψ, h1, h2, h3, h4⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_isCharAF (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyReal F) :
    ∃ ψ, IsCharAF F ψ :=
  exists_isCharAF_of_std PI.Bridge.bridge_stdAddChar F hF

end GlobalTheory.CompanionTheory.AdelicChar
