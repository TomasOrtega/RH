import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.WeilBound.ThetaLifts.LatticeBasics.LocDistE

namespace GlobalTheory.ThK.Dbl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem locDist : LocDist := by
  intro F _ _ v n d ξ hξ l hl
  have : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v
  have : LocallyCompactSpace (Fv F v) := inferInstance
  have : NonarchimedeanAddGroup (Fv F v) := by
    refine ⟨fun U hU => ?_⟩
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
    exact ⟨⟨(Valued.v.restrict.ltAddSubgroup γ), Valued.isOpen_ball _ _⟩, hγ⟩
  refine ⟨fun h => LD.lt_case ξ _ hξ h l hl, ?_⟩
  rintro rfl φ hφ g
  exact LD.eq_case ξ _ hξ l hl g φ hφ

end GlobalTheory.ThK.Dbl
