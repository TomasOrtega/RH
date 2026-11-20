import Mathlib
import Formalism.PeriodIntegrals.LatMin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinimalLatticeNorm.NormTwoEqOne

namespace PI

/- English proof (translation)
Introduce `p _ σ B L W hp2 _ _ hL hsm hadd hsym hne`. Use `PI.LatMinWork.main hp2 B L hL ?_ hadd hsym hne` and prove the remaining obligations. Introduce `c u v`. Establish `h : c • u = (c : ℚ_[p]) • u` using `(algebraMap_smul ℚ_[p] c u).symm`. Rewrite using `[h, hsm]`.
-/
theorem exists_minimalNormVector : PI.LatMin := by
  intro p _ σ B L W hp2 _ _ hL hsm hadd hsym hne
  refine PI.LatMinWork.main hp2 B L hL ?_ hadd hsym hne
  intro c u v
  have h : c • u = (c : ℚ_[p]) • u := (algebraMap_smul ℚ_[p] c u).symm
  rw [h, hsm]

end PI
