import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeAlgebraStructure
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHeckeAlgebraStructure.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.hecke_algebra_structure : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAlg.hk_alg | exact GlobalTheory.CompanionTheory.HeckeAlg.hk_alg | (intros; apply GlobalTheory.CompanionTheory.HeckeAlg.hk_alg <;> assumption)
