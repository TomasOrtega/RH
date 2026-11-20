import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplex
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHaarRightInvariantTotallyComplex.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.haar_right_invariant_totally_complex : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.GAUnimod.isMulRightInvariant_haar_GA | exact GlobalTheory.CompanionTheory.GAUnimod.isMulRightInvariant_haar_GA | (intros; apply GlobalTheory.CompanionTheory.GAUnimod.isMulRightInvariant_haar_GA <;> assumption)
