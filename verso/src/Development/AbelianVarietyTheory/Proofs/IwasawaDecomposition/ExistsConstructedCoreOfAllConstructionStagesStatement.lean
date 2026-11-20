import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstructedCoreOfAllConstructionStages
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsConstructedCoreOfAllConstructionStages.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.exists_constructedCore_of_all_construction_stages : StandardLattice.SiegelMassRatioCM → ∀ 𝒮 : Slots, AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 → StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core | exact GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core | (intros; apply GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core <;> assumption)
