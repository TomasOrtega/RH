import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PLinChange
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PRadial
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PAmbChart
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PAmbEq
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PChartIndep
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PAmbUnitary
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PUnitaryInv
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PFormIntegral
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PPairMk
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PInnerSelf
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.L2Inner
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.DiagUnitary
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PParseval
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PDefinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

/- English proof (translation)
The claim follows from `LinChange.proof`.
-/
theorem LinChange.full : LinChange.Statement := LinChange.proof
/- English proof (translation)
The claim follows from `Radial.proof`.
-/
theorem Radial.full : Radial.Statement := Radial.proof
/- English proof (translation)
The claim follows from `AmbChart.proof LinChange.full Radial.full`.
-/
theorem AmbChart.full : AmbChart.Statement := AmbChart.proof LinChange.full Radial.full
/- English proof (translation)
The claim follows from `AmbEq.proof AmbChart.full`.
-/
theorem AmbEq.full : AmbEq.Statement := AmbEq.proof AmbChart.full
/- English proof (translation)
The claim follows from `ChartIndep.proof AmbChart.full`.
-/
theorem ChartIndep.full : ChartIndep.Statement := ChartIndep.proof AmbChart.full
/- English proof (translation)
The claim follows from `AmbUnitary.proof LinChange.full`.
-/
theorem AmbUnitary.full : AmbUnitary.Statement := AmbUnitary.proof LinChange.full
/- English proof (translation)
The claim follows from `UnitaryInv.proof AmbEq.full AmbUnitary.full`.
-/
theorem UnitaryInv.full : UnitaryInv.Statement := UnitaryInv.proof AmbEq.full AmbUnitary.full
/- English proof (translation)
The claim follows from `FormIntegral.proof ChartIndep.full`.
-/
theorem FormIntegral.full : FormIntegral.Statement := FormIntegral.proof ChartIndep.full
/- English proof (translation)
The claim follows from `PairMk.proof`.
-/
theorem PairMk.full : PairMk.Statement := PairMk.proof
/- English proof (translation)
The claim follows from `InnerSelf.proof`.
-/
theorem InnerSelf.full : InnerSelf.Statement := InnerSelf.proof
/- English proof (translation)
The claim follows from `Sesq.proof PairMk.full`.
-/
theorem Sesq.full : Sesq.Statement := Sesq.proof PairMk.full
/- English proof (translation)
The claim follows from `Orth.proof UnitaryInv.full PairMk.full`.
-/
theorem Orth.full : Orth.Statement := Orth.proof UnitaryInv.full PairMk.full
/- English proof (translation)
The claim follows from `Parseval.proof Orth.full Sesq.full InnerSelf.full`.
-/
theorem Parseval.full : Parseval.Statement := Parseval.proof Orth.full Sesq.full InnerSelf.full
/- English proof (translation)
The claim follows from `Definite.proof Parseval.full InnerSelf.full`.
-/
theorem Definite.full : Definite.Statement := Definite.proof Parseval.full InnerSelf.full

end FSInv

namespace CP

variable {N : ℕ}

end CP

end

end GroundTheory.Heights₂.Heights
