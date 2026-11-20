import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueAlgebraUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FResidueAlgebraUnramified.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.residue_algebra_unramified : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad | exact GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad | (intros; apply GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad <;> assumption)
