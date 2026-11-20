import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormFibreCardNonzero.lean&line=297#L297)
-/
theorem _root_.GlobalTheory.T.norm_fibre_card_nonzero : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ t : E, τ t = t → t ≠ 0 → (Nat.card {a : E // a * τ a = t} : ℤ) = q - ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre | exact GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre | (intros; apply GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre <;> assumption)
