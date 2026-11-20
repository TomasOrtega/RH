import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactColumnsNormLowerBound
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.AdelicColumnK.column_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCompactColumnsNormLowerBound.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.compact_columns_norm_lower_bound : ∀ (K : Type) [Field K] [NumberField K] (C : Set (AdelicGLn.AdelicGL K 3)), IsCompact C → ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ C, ∀ j : Fin 3, Reduction.HasFiniteContent (fun i => (m : Matrix (Fin 3) (Fin 3) 𝔸[K]) i j) ∧ ε ≤ Reduction.adelicNorm (fun i => (m : Matrix (Fin 3) (Fin 3) 𝔸[K]) i j) := by
  first | exact @GlobalTheory.CompanionTheory.AdelicColumnK.column_bound | exact GlobalTheory.CompanionTheory.AdelicColumnK.column_bound | (intros; apply GlobalTheory.CompanionTheory.AdelicColumnK.column_bound <;> assumption)
