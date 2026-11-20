import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lv3StageMovesSpectral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeightCounting.Up.lv3Mv_true` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLv3StageMovesSpectral.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.lv3Mv_prmR_NEo_and_NEog : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (S : SExt) (Γ : GeoP), LevelThreeCondition (prmR (NEo hL cDep) S Γ).s ∧ LevelThreeCondition (prmR (NEog hL cDep) S Γ).s := by
  first | exact @GlobalTheory.HeightCounting.Up.lv3Mv_true | exact GlobalTheory.HeightCounting.Up.lv3Mv_true | (intros; apply GlobalTheory.HeightCounting.Up.lv3Mv_true <;> assumption)
