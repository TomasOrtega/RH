import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMemCuspFormsOfActionLaws
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLevelActionMemCuspFormsOfActionLaws.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.levelAction_mem_cuspForms_of_action_laws : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → ∀ g, (∀ a, (lev g).2 a = a) → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := by
  first | exact @GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev | exact GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev | (intros; apply GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev <;> assumption)
