import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Central
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Tensor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliWhittakerZero

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

universe u v

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem capelliCentral : CapelliCentralStatement.{u} := by
  intro 𝒰 _ _ n E x hE a b
  exact capelliC_central E hE x a b

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem capelliExpand : CapelliExpandStatement.{u} := by
  intro 𝒰 _ _ m E om hE
  exact ⟨fun b c => capelli_expand_plus E hE om b c, fun a c => capelli_expand_minus E hE om a c⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem capelliTensor : CapelliTensorStatement.{u} := by
  intro M _ _ n E hE
  exact ⟨isGlRep_tensV E hE, isGlRep_tensVd E hE, casimir_tensV E, casimir_tensVd E⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem capelliAPlus : CapelliAPlusStatement.{u} := by
  intro M _ _ m E y om v hE hv
  exact eeV_nnPlus E hE y om v hv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem capelliAMinus : CapelliAMinusStatement.{u} := by
  intro M _ _ m E β om v hE hv
  exact eeVd_nnMinus E hE β om v hv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem capelliB : CapelliBStatement.{u, v} := by
  intro M R _ _ _ _ k r E D ψ l x hE hr hl hψ hD
  exact capelli_whittaker k r E D ψ l x hE hr hl hψ hD

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem whittakerZeroStatement : WhittakerZeroStatement.{u, v} := by
  intro M R _ _ _ _ k E D l x hD
  exact capelli_whittaker_zero k E D l x hD

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
