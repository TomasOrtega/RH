import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.IsImgTrans
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.KsetMulVecMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StHOfOpen

noncomputable section

namespace PIW.AdelClassFin

/- English proof (translation)
The claim follows from `stKFin_of (stLatFin_of lattice_dense)`.
-/
theorem stKFin : StKFin := stKFin_of (stLatFin_of lattice_dense)

/- English proof (translation)
The claim follows from `stTop stCong stKFin (stGenusOf stDict h)`.
-/
theorem adelClassFin_of_H (h : StH) : PI.AdelClassFin.AdelClassFin :=
  stTop stCong stKFin (stGenusOf stDict h)

/- English proof (translation)
The claim follows from `adelClassFin_of_H (stH_of_open h1 h2 h3 h4 h5 h6 h7)`.
-/
theorem adelClassFin_of_open (h1 : SpOne) (h2 : IdealBoundAll) (h3 : SvMajE) (h4 : SvCodiff) (h5 : SvBasis)
    (h6 : SvGramDet) (h7 : SvReal) : PI.AdelClassFin.AdelClassFin :=
  adelClassFin_of_H (stH_of_open h1 h2 h3 h4 h5 h6 h7)

end PIW.AdelClassFin
