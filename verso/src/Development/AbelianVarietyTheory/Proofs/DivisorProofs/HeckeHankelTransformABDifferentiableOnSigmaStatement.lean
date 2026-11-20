import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABDifferentiableOnSigma
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTransABTwoZero
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeTwo.hTransAB_differentiableOn` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckeHankelTransformABDifferentiableOnSigma.lean&line=163#L163)
-/
theorem _root_.GlobalTheory.T.heckeHankelTransformAB_differentiableOn_sigma : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.hTransAB_differentiableOn | exact GlobalTheory.HeckeTwo.hTransAB_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.hTransAB_differentiableOn <;> assumption)
