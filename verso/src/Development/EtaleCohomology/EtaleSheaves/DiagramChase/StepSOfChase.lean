import Development.EtaleCohomology.EtaleSheaves.DiagramChase

namespace LateralTheory.E.StepSPf

/- English proof (translation)
The claim follows from `S_of_restr_chase restr hC`.
-/
theorem StepS_of_chase (hC : DiagramChase₂) : LateralTheory.E.ContStepPf.StepS := S_of_restr_chase restr hC

end LateralTheory.E.StepSPf
