import Mathlib

namespace UpperTheory.V.QbarInst

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem charZero : CharZero (AlgebraicClosure ℚ) := inferInstance

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem torsionFree : Module.IsTorsionFree ℚ (AlgebraicClosure ℚ) := inferInstance

/- English proof (translation)
The claim follows from `AlgebraicClosure.instIsAlgClosure ℚ`.
-/
theorem algClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ

end UpperTheory.V.QbarInst
