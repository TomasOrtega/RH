import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionMeetsAbovePlace
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSectionMeetsAbovePlace.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.section_meets_above_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ v : PlF E, ∃ w : Above v, w.1 ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section | exact GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section | (intros; apply GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section <;> assumption)
