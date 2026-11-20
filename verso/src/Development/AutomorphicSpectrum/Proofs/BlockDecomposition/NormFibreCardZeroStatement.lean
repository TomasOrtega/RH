import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormFibreCardZero.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.norm_fibre_card_zero : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → (Nat.card {a : E // a * τ a = 0} : ℤ) = q * (1 + ε) - ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero | exact GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero | (intros; apply GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero <;> assumption)
