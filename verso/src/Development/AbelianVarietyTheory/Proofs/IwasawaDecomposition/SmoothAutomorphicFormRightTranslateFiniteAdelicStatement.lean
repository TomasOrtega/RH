import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSmoothAutomorphicFormRightTranslateFiniteAdelic.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.smoothAutomorphicForm_rightTranslate_finiteAdelic : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ k ∈ GfC V, IsAutFunSm θ V (rTr V k φ) := by
  first | exact @GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin | exact GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin | (intros; apply GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin <;> assumption)
