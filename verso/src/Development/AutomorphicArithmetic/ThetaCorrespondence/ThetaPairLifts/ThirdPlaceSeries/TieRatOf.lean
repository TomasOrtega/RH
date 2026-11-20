import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfTwistRow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem tieRat_of_alt (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hR : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace) : _root_.GlobalTheory.BigOn.Exp.CompatibilityRational := by
  unfold _root_.GlobalTheory.BigOn.Exp.CompatibilityRational _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hA hR).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j Z => ?_⟩
  obtain ⟨hA', hR'⟩ := hx0 x hx hle i p hp
  have hrow := hR' hm w hw j Z.ρ Z.good Z.pin (levelOf_exportTie Z)
  have hs := Z.scalar ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hrat := hs.rat hrow
  obtain ⟨ν, hn, -⟩ := hrow
  obtain ⟨hok, hcl, -⟩ := hA' hm w hw j
  exact ⟨hs.norm ⟨ν, hn⟩, hrat.1, fun s h P hd => hrat.2.1 _ _ _ hok hcl s h P hd⟩
end GlobalTheory.BigOn.Exp
end
