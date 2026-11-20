import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentatives
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHeckeCosetRepresentatives.lean&line=283#L283)
-/
theorem _root_.GlobalTheory.T.hecke_coset_representatives : Ad3.R.C0 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant | exact GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant | (intros; apply GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant <;> assumption)
