import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssembly
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.EisCore.wall_core` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPrincipalIdentityAssembly.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.principal_identity_assembly : EpMain → DGood → Master → SideOf → Term → ZetaK → SideUnfold → SideConv → ZetaOne → Core := by
  first | exact @GlobalTheory.CompanionTheory.EisCore.wall_core | exact GlobalTheory.CompanionTheory.EisCore.wall_core | (intros; apply GlobalTheory.CompanionTheory.EisCore.wall_core <;> assumption)
