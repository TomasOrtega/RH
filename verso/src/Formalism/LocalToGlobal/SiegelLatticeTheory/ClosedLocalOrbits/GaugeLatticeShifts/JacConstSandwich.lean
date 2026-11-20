import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwSandwichOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwGaussUniq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiForm
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwBigCellG
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiDeriv
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHR
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim

namespace Formalism.L2.SG.Pf.BH

/- English proof (translation)
Use `sandwich_of_chart Sw.lieG' Sw.lieWb' gauss_sum_unique phi_form' big_cell_g (phiDeriv_of Sw.w0Sq) Sw.lIso Sw.w0Sq ?_ ?_` and prove the remaining obligations. Unfold `PI.SwSand.LieEN`. Use `intros`. Conclude with `Formalism.MainNotions.BridgeCSB.lieE_N`. Use `intros`.

Apply `Formalism.MainNotions.BridgeCSB.exp_mem_N` to reduce the goal to its premises.
-/
theorem sandwich' : Sandwich := by
  refine sandwich_of_chart Sw.lieG' Sw.lieWb' gauss_sum_unique phi_form' big_cell_g
    (phiDeriv_of Sw.w0Sq) Sw.lIso Sw.w0Sq ?_ ?_
  · unfold PI.SwSand.LieEN
    intros
    exact Formalism.MainNotions.BridgeCSB.lieE_N
  · intros
    apply Formalism.MainNotions.BridgeCSB.exp_mem_N

end Formalism.L2.SG.Pf.BH
