import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstPush
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem frame_independent_at_infinity : FrameIndependentAtInfinity := by
  intro D X u' ψ hT μinf νinf fibInf hH
  have h := (orbM_mem X u' hT (detNZ_holds X u' ψ hT μinf νinf fibInf hH) 1).2
  have h2 : orbM X u' 1 = Y0 X u' := one_smul _ _
  rwa [h2] at h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem constTest_of_polar_prop (hP : PolarLoc) (hPr : ProperOrb) : ConstTest :=
  constTest_of_polar_proper hP frame_independent_at_infinity hPr

end PI.AprimeInfW
