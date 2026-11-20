import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob

namespace Formalism.L2.SG.Pf.StabIntSh

/- English proof (translation)
The claim follows from `stabIntShape_of locShapeL locShapeG locGlob shapeNZ`.
-/
theorem stabIntShape (D : Formalism.BasicNotions.D7) : StabIntShapeC D :=
  stabIntShape_of locShapeL locShapeG locGlob shapeNZ

end Formalism.L2.SG.Pf.StabIntSh
