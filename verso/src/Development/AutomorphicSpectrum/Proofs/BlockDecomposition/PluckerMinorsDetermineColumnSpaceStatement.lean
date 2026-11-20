import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PluckerMinorsDetermineColumnSpace
import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GodementH.Cramer.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPluckerMinorsDetermineColumnSpace.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.plucker_minors_determine_column_space : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι),
    mnr M f₀ ≠ 0 → mnr M' f₀' ≠ 0 → (∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') → ∃ c : GL (Fin n) K, M' = M * c.1 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.Cramer.main | exact GlobalTheory.CompanionTheory.GodementH.Cramer.main | (intros; apply GlobalTheory.CompanionTheory.GodementH.Cramer.main <;> assumption)
