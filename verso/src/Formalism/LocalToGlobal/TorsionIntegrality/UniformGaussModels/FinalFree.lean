import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementK
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementL
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.HalfMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.TwoIsogenyDiscriminantRatioCubic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ChainPC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ExistsNormEqTwoPow
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.HermFrameHolds
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.H (localStandard kappaExists)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frameExistsH : FrameExistsH := FrP.hermFrame_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uniformGaussModels_fact_variant : ThetaFourthPowerShapeNormalised := theta_kappa_shape_holds localStandard kappaExists

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem frobExistsH : FrobExistsH := by
  intro l _ hl
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.kurFrob l (by omega)
  exact ⟨σ, hσ⟩

end Formalism.L2.Th1.Top
