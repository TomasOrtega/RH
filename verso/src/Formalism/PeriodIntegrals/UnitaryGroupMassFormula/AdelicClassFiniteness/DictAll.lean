import Mathlib
import Formalism.PeriodIntegrals.AdelClassFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StGenusOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictPlan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictInter
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictTop

namespace PIW.AdelClassFin

/- English proof (translation)
The claim follows from `lInter_of dual_intersection`.
-/
theorem lattice_intersection' : LInter := lInter_of dual_intersection
/- English proof (translation)
The claim follows from `lDenom_of dual_denominator`.
-/
theorem lattice_denominator : LDenom := lDenom_of dual_denominator
/- English proof (translation)
The claim follows from `lDense_of dual_dense`.
-/
theorem lattice_dense : LDense := lDense_of dual_dense
/- English proof (translation)
The claim follows from `lHatDual_of dual_intersection lattice_denominator lattice_dense dual_hat_integral`.
-/
theorem dual_hat_lattice : LHatDual := lHatDual_of dual_intersection lattice_denominator lattice_dense dual_hat_integral
/- English proof (translation)
The claim follows from `mLat_of lattice_intersection' lattice_denominator`.
-/
theorem lattice_m_is_lattice : MLat := mLat_of lattice_intersection' lattice_denominator
/- English proof (translation)
The claim follows from `mGen_of lattice_denominator lattice_dense`.
-/
theorem lattice_m_generation : MGen := mGen_of lattice_denominator lattice_dense
/- English proof (translation)
The claim follows from `mDual_of dual_intersection dual_hat_integral dual_hat_lattice lattice_m_generation`.
-/
theorem lattice_m_dual : MDual := mDual_of dual_intersection dual_hat_integral dual_hat_lattice lattice_m_generation
/- English proof (translation)
The claim follows from `mInj_of lattice_m_generation`.
-/
theorem lattice_map_injective : MInj := mInj_of lattice_m_generation

/- English proof (translation)
The claim follows from `stDict_of lattice_m_is_lattice lattice_m_dual lattice_map_injective lattice_m_equiv`.
-/
theorem stDict : StDict := stDict_of lattice_m_is_lattice lattice_m_dual lattice_map_injective lattice_m_equiv

end PIW.AdelClassFin
