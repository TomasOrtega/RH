import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGIs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsGIs.lean&line=162#L162)
-/
theorem _root_.GlobalTheory.T.exists_GJStage_GIs2_pinned : StepW Pinned fun K B f T w => ∃ G : GJStage B w.C, GIs2 K w G := by
  first | exact @GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep | exact GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep | (intros; apply GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep <;> assumption)
