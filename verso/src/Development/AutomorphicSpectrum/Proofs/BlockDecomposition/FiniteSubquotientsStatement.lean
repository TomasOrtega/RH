import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotients
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RepFinSubq.finSubq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteSubquotients.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.finite_subquotients : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], FinSubq F ι := by
  first | exact @GlobalTheory.CompanionTheory.RepFinSubq.finSubq | exact GlobalTheory.CompanionTheory.RepFinSubq.finSubq | (intros; apply GlobalTheory.CompanionTheory.RepFinSubq.finSubq <;> assumption)
