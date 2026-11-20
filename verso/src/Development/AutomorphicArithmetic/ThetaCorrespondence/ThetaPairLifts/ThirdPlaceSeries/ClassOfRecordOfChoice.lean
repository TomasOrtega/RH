import Formalism.LocalToGlobal.ClassOfRecordOfChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
namespace Formalism.L2.Top3
/- English proof (translation)
Assemble the required witnesses or components as `⟨s.1, fun x hx h i => ⟨(s.2 x hx h i).T.toTiedDataS⟩⟩`.
-/
theorem tied_families_of_choice_alt {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) : _root_.Formalism.L2.SecondChernLinkedClass Fm :=
  ⟨s.1, fun x hx h i => ⟨(s.2 x hx h i).T.toTiedDataS⟩⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨_root_.Formalism.L2.Top3.tied_families_of_choice_alt s, h.1⟩, h.2.2.1, h.2.2.2.1⟩`.
-/
theorem linkedFamiliesAligned_of_duty {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) (h : Duty Fm) : _root_.Formalism.L2.LinkedFamiliesAligned' Fm :=
  ⟨⟨_root_.Formalism.L2.Top3.tied_families_of_choice_alt s, h.1⟩, h.2.2.1, h.2.2.2.1⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨s.tiedRec, h⟩`.
-/
theorem layerTwoFamilyClass_of_linked_aligned {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) (h : _root_.Formalism.L2.LinkedFamiliesAligned' Fm) : _root_.Formalism.L2.SecondLayerFamilyClass Fm :=
  ⟨s.tiedRec, h⟩
abbrev SelectionDefiniteHeightCondition (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {p : ℕ × ℕ // (Fm.D x i).s.Del = (p.1 : ℚ) ∧ (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (p.2 : ℝ)}
section ColChoice
end ColChoice
end Formalism.L2.Top3
end
end
