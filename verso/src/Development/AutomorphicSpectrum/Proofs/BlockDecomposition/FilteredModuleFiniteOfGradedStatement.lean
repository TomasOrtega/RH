import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredModuleFiniteOfGraded
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LenDev.finite_H_sq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFilteredModuleFiniteOfGraded.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.filtered_module_finite_of_graded : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (Fil : ℤ → IdF A),
    (∀ r r' : ℤ, r ≤ r' → ∀ T, (Fil r').S T ≤ (Fil r).S T) → ∀ s : ℕ,
    (∀ r : ℕ, r < s → ∀ j, Module.Finite R (CH.H (sq (Fil r) (Fil ((r : ℤ) + 1))) j)) →
    ∀ j, Module.Finite R (CH.H (sq (Fil 0) (Fil s)) j) := by
  first | exact @GlobalTheory.CompanionTheory.LenDev.finite_H_sq | exact GlobalTheory.CompanionTheory.LenDev.finite_H_sq | (intros; apply GlobalTheory.CompanionTheory.LenDev.finite_H_sq <;> assumption)
