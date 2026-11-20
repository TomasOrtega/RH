import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCard
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedQuotientCard.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.unramified_quotient_card : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ k : ℕ, Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_quot_lev | exact GlobalTheory.CompanionTheory.UnrDens.card_quot_lev | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_quot_lev <;> assumption)
