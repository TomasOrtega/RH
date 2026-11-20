import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsolateRepresentationAtCharacter
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIsolateRepresentationAtCharacter.lean&line=446#L446)
-/
theorem _root_.GlobalTheory.T.isolate_representation_at_character : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], IsolateAt F ι := by
  first | exact @GlobalTheory.CompanionTheory.Isolate.isolateAt | exact GlobalTheory.CompanionTheory.Isolate.isolateAt | (intros; apply GlobalTheory.CompanionTheory.Isolate.isolateAt <;> assumption)
