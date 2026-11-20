import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SOfStar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SPairs
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecT

set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.GalS
/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem bridgeStar_alt : GlobalTheory.Published.GelfandKazhdanDual → (_root_.UpperTheory.One.M.Row → _root_.UpperTheory.GalS.CarUAlt) ∧ (_root_.UpperTheory.GalS.PairUAlt → _root_.UpperTheory.GalS.CuspUAlt) :=
  fun hGK => ⟨_root_.UpperTheory.GalS.ofDual_star_alt hGK, _root_.UpperTheory.GalS.cusp_of_pair_alt hGK⟩
end UpperTheory.GalS
end
