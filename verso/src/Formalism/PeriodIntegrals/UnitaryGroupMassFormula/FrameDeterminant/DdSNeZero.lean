import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.FrameB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.DetOfFrame

noncomputable section

open NumberField

namespace PI.TripleFrameDeterminant.W

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.IsoDetDefs PI.FlagFrameDeterminants

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Unfold `ddS`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Rewrite using `[Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `differentIdeal_ne_bot`.
-/
theorem ddS_ne_zero (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
  exact differentIdeal_ne_bot

end PI.TripleFrameDeterminant.W
