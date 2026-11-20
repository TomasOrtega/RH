import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMajorant
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FOrbitMajorant.lean&line=234#L234)
-/
theorem _root_.GlobalTheory.T.orbit_majorant : OrbitMaj := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.orbitMaj | exact GlobalTheory.CompanionTheory.ThTot.orbitMaj | (intros; apply GlobalTheory.CompanionTheory.ThTot.orbitMaj <;> assumption)
