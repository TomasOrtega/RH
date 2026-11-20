import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluing
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEisensteinGluing.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.eisenstein_gluing : Glue := by
  first | exact @GlobalTheory.CompanionTheory.PolyDenominator.glue | exact GlobalTheory.CompanionTheory.PolyDenominator.glue | (intros; apply GlobalTheory.CompanionTheory.PolyDenominator.glue <;> assumption)
