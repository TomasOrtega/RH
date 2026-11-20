import Mathlib
import Formalism.PeriodIntegrals.BiaddOfCube
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditiveCubes.ConstantCoeffLogEqZero

/- English proof (translation)
Introduce `p _ l ex ph hex h hC`. Establish `hxz : PI.BiaddOfCube.add l ex (PI.BiaddOfCube.Xv (p` using `p) 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.BiaddOfCube.Xv 2) = PI.BiaddOfCube.add l ex (PI.BiaddOfCube.Xv 2) (PI.BiaddOfCube.Xv 0) := PI.BiaddOfCubeWork.add_comm' l ex _ _`. Establish `has` using `PI.BiaddOfCubeWork.add_assoc' hex h (PI.BiaddOfCube.Xv (p := p) 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.BiaddOfCube.Xv 1) (PI.BiaddOfCube.Xv 2) (PI.BiaddOfCubeWork.cc_Xv 0) (PI.BiaddOfCubeWork.cc_Xv 1) (PI.BiaddOfCubeWork.cc_Xv 2)`. Prove the components needed by the constructor for the conclusion. Use `PI.BiaddOfCubeWork.simeq_of_sub_eq ?_ hC` and prove the remaining obligations.

Simplify using `only [PI.BiaddOfCube.be, hxz]`. Expand and normalize the polynomial expressions, which then agree. Use `PI.BiaddOfCubeWork.simeq_of_sub_eq ?_ hC` and prove the remaining obligations. Simplify using `only [PI.BiaddOfCube.be, hxz, ← has]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem biadditiveOfCube_holds : PI.BiaddOfCube.Target := by
  intro p _ l ex ph hex h hC
  have hxz : PI.BiaddOfCube.add l ex (PI.BiaddOfCube.Xv (p := p) 0 : MvPowerSeries (Fin 3) ℂ_[p])
      (PI.BiaddOfCube.Xv 2) = PI.BiaddOfCube.add l ex (PI.BiaddOfCube.Xv 2) (PI.BiaddOfCube.Xv 0) :=
    PI.BiaddOfCubeWork.add_comm' l ex _ _
  have has := PI.BiaddOfCubeWork.add_assoc' hex h
    (PI.BiaddOfCube.Xv (p := p) 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.BiaddOfCube.Xv 1) (PI.BiaddOfCube.Xv 2)
    (PI.BiaddOfCubeWork.cc_Xv 0) (PI.BiaddOfCubeWork.cc_Xv 1) (PI.BiaddOfCubeWork.cc_Xv 2)
  constructor
  · refine PI.BiaddOfCubeWork.simeq_of_sub_eq ?_ hC
    simp only [PI.BiaddOfCube.be, hxz]
    ring
  · refine PI.BiaddOfCubeWork.simeq_of_sub_eq ?_ hC
    simp only [PI.BiaddOfCube.be, hxz, ← has]
    ring
