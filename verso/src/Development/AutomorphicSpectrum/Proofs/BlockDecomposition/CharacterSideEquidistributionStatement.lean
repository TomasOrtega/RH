import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterSideEquidistribution
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCharacterSideEquidistribution.lean&line=146#L146)
-/
theorem _root_.GlobalTheory.T.character_side_equidistribution : PositivityTheory.Rg.Mass.Equi → PsiSide := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.psiSide_of_equi | exact GlobalTheory.CompanionTheory.BasePsi.psiSide_of_equi | (intros; apply GlobalTheory.CompanionTheory.BasePsi.psiSide_of_equi <;> assumption)
