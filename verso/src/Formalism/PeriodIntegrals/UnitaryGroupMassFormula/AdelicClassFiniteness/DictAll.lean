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
A detailed English derivation is pending.
-/
theorem lattice_intersection' : LInter := lInter_of dual_intersection
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_denominator : LDenom := lDenom_of dual_denominator
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_dense : LDense := lDense_of dual_dense
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dual_hat_lattice : LHatDual := lHatDual_of dual_intersection lattice_denominator lattice_dense dual_hat_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_m_is_lattice : MLat := mLat_of lattice_intersection' lattice_denominator
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_m_generation : MGen := mGen_of lattice_denominator lattice_dense
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_m_dual : MDual := mDual_of dual_intersection dual_hat_integral dual_hat_lattice lattice_m_generation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_map_injective : MInj := mInj_of lattice_m_generation

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stDict : StDict := stDict_of lattice_m_is_lattice lattice_m_dual lattice_map_injective lattice_m_equiv

end PIW.AdelClassFin
