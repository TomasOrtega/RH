import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLiftGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLift

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

def RFinMax : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → {m : Ideal M.R | m.IsMaximal}.Finite

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem srLift_of_finMax (h : RFinMax) : SRLift := by
  intro F _ _ _ E _ _ _ _ M hOK n A K hA hK
  exact Formalism.L2.SG.Pf.SRL.srLift_of_finite (h M hOK) A K hA hK

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
