import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProducts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ProdLen.prodFinLen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteLengthOfProducts.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.finite_length_of_products : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], ProdFinLen F ι := by
  first | exact @GlobalTheory.CompanionTheory.ProdLen.prodFinLen | exact GlobalTheory.CompanionTheory.ProdLen.prodFinLen | (intros; apply GlobalTheory.CompanionTheory.ProdLen.prodFinLen <;> assumption)
