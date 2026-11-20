import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFactorsLocalUnitsAlmostAll
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFrameFactorsLocalUnitsAlmostAll.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.frame_factors_local_units_almost_all : ∀ (D : D7) (Z : LocDat D) (a : Fin (D.R.rS + 1)),
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) (frFac Z.δ p a)}.Finite := by
  first | exact @GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite | exact GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite | (intros; apply GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite <;> assumption)
