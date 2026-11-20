import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeTwo.aPart_differentiableOn` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckeEisensteinConstantTermPartDifferentiableOn.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.heckeEisensteinConstantTermPart_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (GlobalTheory.HeckeTwo.aPart 𝔞) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.aPart_differentiableOn | exact GlobalTheory.HeckeTwo.aPart_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.aPart_differentiableOn <;> assumption)
