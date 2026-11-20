import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DcosProduct.dcosMul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDoubleCosetMultiplication.lean&line=269#L269)
-/
theorem _root_.GlobalTheory.T.double_coset_multiplication : DcosMul := by
  first | exact @GlobalTheory.CompanionTheory.DcosProduct.dcosMul | exact GlobalTheory.CompanionTheory.DcosProduct.dcosMul | (intros; apply GlobalTheory.CompanionTheory.DcosProduct.dcosMul <;> assumption)
