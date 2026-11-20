import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLaplacianLocalFormulaSphere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BcUnique.loc_ddc_snd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDdcLaplacianLocalFormulaSphere.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.ddc_laplacian_local_formula_sphere : ∀ (M : Type) [TopologicalSpace M] (A : HolAtlas M 1) (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → ∀ (j : A.ι) (x : V (1 + 1)), x ∈ ((famAtlas A).e (j, sphFin)).target → (famAtlas A).loc ((famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ)) (j, sphFin) x = ((Laplacian.laplacian φ (x (Fin.last 1)) / (4 * π) : ℝ) : ℂ) • ((Complex.I / 2) • (dz (Fin.last 1) * dzb (Fin.last 1))) := by
  first | exact @GlobalTheory.BcUnique.loc_ddc_snd | exact GlobalTheory.BcUnique.loc_ddc_snd | (intros; apply GlobalTheory.BcUnique.loc_ddc_snd <;> assumption)
