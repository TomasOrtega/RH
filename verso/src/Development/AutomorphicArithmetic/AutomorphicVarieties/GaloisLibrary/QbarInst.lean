import Mathlib

namespace UpperTheory.V.QbarInst

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem charZero : CharZero (AlgebraicClosure ℚ) := inferInstance

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem torsionFree : Module.IsTorsionFree ℚ (AlgebraicClosure ℚ) := inferInstance

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem algClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ

end UpperTheory.V.QbarInst
