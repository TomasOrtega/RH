import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne | exact GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne | (intros; apply GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.spherical_one_of_local_algebra : LocAlg → SphOne := by
  first | exact @GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne | exact GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne | (intros; apply GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne <;> assumption)
