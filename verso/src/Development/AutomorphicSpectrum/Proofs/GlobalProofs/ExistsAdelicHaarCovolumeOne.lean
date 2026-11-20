import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem exists_isCovolOne : ∀ (F : Type) [Field F] [NumberField F], ∃ db : Measure (AF F), IsCovolOne db := by
  intro F _ _
  have e : (measAF : MeasurableSpace (AF F)) = GroundTheory.Global.measurableSpace_adeleRing F :=
    (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm
  unfold IsCovolOne
  rw [e]
  refine ⟨GroundTheory.Global.adeleMeasure F, inferInstance, GroundTheory.Global.fundamentalSet F, ?_,
    GroundTheory.Global.adeleMeasure_fundamentalSet F⟩
  exact GroundTheory.Global.isAddFundamentalDomain_fundamentalSet F

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV
