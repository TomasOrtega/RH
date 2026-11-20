import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiagonalFormCounting
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapesTer
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingData

namespace Formalism.L2.SG.Pf.Cnt

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem alpha_discriminant_holds : AlphaDisc :=
  Formalism.L2.SG.Pf.G5.alphaDisc_of_discOnto
    (Formalism.L2.SG.Pf.discriminantNormShapes.discOnto_of_uDModel Formalism.L2.SG.Pf.Cnt.unitary_discriminant_model)

end Formalism.L2.SG.Pf.Cnt
