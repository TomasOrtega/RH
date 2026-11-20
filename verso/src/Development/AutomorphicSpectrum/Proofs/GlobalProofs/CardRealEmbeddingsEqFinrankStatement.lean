import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardRealEmbeddingsEqFinrank
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FCardRealEmbeddingsEqFinrank.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.card_real_embeddings_eq_finrank : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Finite (F →+* ℝ) ∧ Nat.card (F →+* ℝ) = Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings <;> assumption)
