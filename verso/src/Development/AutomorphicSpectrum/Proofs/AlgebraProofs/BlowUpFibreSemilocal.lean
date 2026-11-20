import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSBlowupfibre

namespace GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre

/- English proof (translation)
The claim follows from `PositivityTheory.Xgn.t_s_blowupfibre`.
-/
theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} :=
  PositivityTheory.Xgn.t_s_blowupfibre

end GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre
