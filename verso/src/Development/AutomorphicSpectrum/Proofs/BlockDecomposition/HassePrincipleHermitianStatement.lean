import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleHermitian
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHassePrincipleHermitian.lean&line=130#L130)
-/
theorem _root_.GlobalTheory.T.hasse_principle_hermitian : Hasse := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseHasse.hasse | exact GlobalTheory.CompanionTheory.SW.BaseHasse.hasse | (intros; apply GlobalTheory.CompanionTheory.SW.BaseHasse.hasse <;> assumption)
