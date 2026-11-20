import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsSmoothCoordinateCover.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.exists_smooth_coordinate_cover : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsSeparated q] [QuasiCompact q],
    (Smooth q → Nonempty (Cov q)) ∧ ∀ d, SmoothOfRelativeDimension d q → ∃ U : Cov q, ∀ α, U.d α = d := by
  first | exact @GlobalTheory.CompanionTheory.CovEx.exists_cov | exact GlobalTheory.CompanionTheory.CovEx.exists_cov | (intros; apply GlobalTheory.CompanionTheory.CovEx.exists_cov <;> assumption)
