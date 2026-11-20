import Mathlib
import Formalism.MirabolicMackeyTheory.StatementC
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.AbsorbLocalConditions
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ErrSum
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.UnipotentNumeric
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsGlobalForm
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.WeightedPlaceLogSum

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

/- English proof (translation)
Introduce `Y hY Q hQ`. Use `le_trans ?_ (Chebyshev.theta_le_log4_mul_x hY)` and prove the remaining obligations. Unfold `Chebyshev.theta`. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_` and prove the remaining obligations. Introduce `p hp`.

Take `⟨h1, h2⟩` from `hQ p hp`. Conclude with `Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h1.pos, Nat.le_floor h2⟩, h1⟩`. Introduce `p _ _`. Conclude with `Real.log_natCast_nonneg p`.
-/
theorem chebyshev_theta_log_four : ThetaLog4 := by
  classical
  intro Y hY Q hQ
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x hY)
  unfold Chebyshev.theta
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := hQ p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h1.pos, Nat.le_floor h2⟩, h1⟩
  · intro p _ _
    exact Real.log_natCast_nonneg p

end Formalism.EigenvalueLevelCeiling
