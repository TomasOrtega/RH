import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParPinsOfRec
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem Base.OtoLL_injective' (B : Base) : Function.Injective B.OtoLL := by
  intro x y h
  apply RingOfIntegers.ext
  exact Subtype.ext h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Supply the required witnesses or components.
-/
theorem hermitianCodeWordStages_ringOfIntegers_full : ∀ X : Stages, OFull X.toD7 := by
  intro X
  refine ⟨X.B.OtoLL_injective', ?_⟩
  let f : X.B.Ks →+* ℂ := X.B.embLL.comp (algebraMap X.B.Ks X.B.LL)
  have hle : FO X.toD7 ≤ f.toRatAlgHom.fieldRange := by
    rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    exact ⟨algebraMap (𝓞 X.B.Ks) X.B.Ks y, rfl⟩
  intro z hz hint
  obtain ⟨x, rfl⟩ := hle hz
  have hx : IsIntegral ℤ x := (isIntegral_algHom_iff f.toIntAlgHom f.injective).1 hint
  exact ⟨(⟨x, hx⟩ : 𝓞 X.B.Ks), rfl⟩

end GlobalTheory.Mem
