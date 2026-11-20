import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsSmoothAutomorphicFunctionTranslateAtRealPlace.lean&line=281#L281)
-/
theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_translate_atRealPlace : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), IsAutFunSm θ V (rTr V (atTau θ V τ g) φ) := by
  first | exact @GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau | exact GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau | (intros; apply GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau <;> assumption)
