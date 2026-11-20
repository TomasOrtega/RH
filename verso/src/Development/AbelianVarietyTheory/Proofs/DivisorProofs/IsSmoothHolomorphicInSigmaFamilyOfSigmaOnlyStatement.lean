import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSmoothHolomorphicInSigmaFamilyOfSigmaOnly.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_of_sigma_only : ∀ (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ), DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) := by
  first | exact @GlobalTheory.HeckeTwo.goodConst | exact GlobalTheory.HeckeTwo.goodConst | (intros; apply GlobalTheory.HeckeTwo.goodConst <;> assumption)
