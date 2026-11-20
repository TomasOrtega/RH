import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegrandUnitMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckeMellinGaussIntegrandUnitMul.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.heckeMellinGaussIntegrand_unit_mul : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ), GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y = GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) * GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  first | exact @GlobalTheory.HeckeShift.term_unit_mul | exact GlobalTheory.HeckeShift.term_unit_mul | (intros; apply GlobalTheory.HeckeShift.term_unit_mul <;> assumption)
