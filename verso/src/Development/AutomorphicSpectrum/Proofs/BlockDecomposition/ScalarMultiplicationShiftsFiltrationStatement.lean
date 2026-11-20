import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltration
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LecShift.leC_shift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FScalarMultiplicationShiftsFiltration.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.scalar_multiplication_shifts_filtration : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := by
  first | exact @GlobalTheory.CompanionTheory.LecShift.leC_shift | exact GlobalTheory.CompanionTheory.LecShift.leC_shift | (intros; apply GlobalTheory.CompanionTheory.LecShift.leC_shift <;> assumption)
