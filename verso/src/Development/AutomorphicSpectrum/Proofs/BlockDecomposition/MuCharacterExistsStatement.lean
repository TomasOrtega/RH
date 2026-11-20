import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuCharacterExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMuCharacterExists.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.mu_character_exists : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e) → MuEx := by
  first | exact @GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists | exact GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists | (intros; apply GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists <;> assumption)
