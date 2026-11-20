import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalModelsUnsplitAlmostAll
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalModelsUnsplitAlmostAll.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.local_models_unsplit_almost_all : ∀ (D : D7) (Z : LocDat D), {p : PlF D | (Z.M p).split ≠ none}.Finite := by
  first | exact @GlobalTheory.LocSplitFinite.split_finite | exact GlobalTheory.LocSplitFinite.split_finite | (intros; apply GlobalTheory.LocSplitFinite.split_finite <;> assumption)
