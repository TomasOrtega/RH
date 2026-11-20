import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteModulesSerreClass.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.finite_modules_serre_class : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∃ 𝒮 : Serre.{1} R,
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ Module.Finite R M := by
  first | exact @GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite | exact GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite | (intros; apply GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite <;> assumption)
