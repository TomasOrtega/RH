import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotentVariant
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSubquotientOfNonNilpotentVariant.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.subquotient_of_non_nilpotent_variant : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], SubOfNonNil' F ι := by
  first | exact @GlobalTheory.CompanionTheory.HeckeSub.subOfNonNil_of_subquot | exact GlobalTheory.CompanionTheory.HeckeSub.subOfNonNil_of_subquot | (intros; apply GlobalTheory.CompanionTheory.HeckeSub.subOfNonNil_of_subquot <;> assumption)
