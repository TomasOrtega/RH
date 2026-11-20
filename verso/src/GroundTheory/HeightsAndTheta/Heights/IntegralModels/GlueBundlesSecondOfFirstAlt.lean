import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSectionNef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem SectionNef.glueBundles_second_of_first (h : _root_.GroundTheory.Heights₂.Heights.Model.SectionNef.Statement) :
    SectionNef.Statement := by
  intro κ _ _ ι _ F _ P hP hd a ha
  have hs : ∃ s : MRing ι F, IsMultiHomog s a ∧ s ∉ P := by
    rcases ha with h1 | h2
    · exact h1
    · exact h2 P hP le_rfl
  obtain ⟨s, hsa, hsP⟩ := hs
  exact h κ ι F P hP hd (fun k => (a k : ℤ)) s 1
    (_root_.GroundTheory.Heights₂.Heights.Model.isRegularSection_form hP.isPrime hsa hsP)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem SectionNef.equiv :
    (_root_.GroundTheory.Heights₂.Heights.Model.SectionNef.Statement ∧
      _root_.GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.Statement) ↔
      SectionNef.Statement :=
  ⟨fun h => SectionNef.glueBundles_second_of_first h.1, fun _ =>
    ⟨_root_.GroundTheory.Heights₂.Heights.Model.SectionNef.proof,
      _root_.GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.proof⟩⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionNef.sectionNef_of_first : SectionNef.Statement :=
  SectionNef.glueBundles_second_of_first _root_.GroundTheory.Heights₂.Heights.Model.SectionNef.proof

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
