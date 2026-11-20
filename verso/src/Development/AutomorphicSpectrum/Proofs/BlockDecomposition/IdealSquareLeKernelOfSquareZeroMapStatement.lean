import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSquareLeKernelOfSquareZeroMap
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIdealSquareLeKernelOfSquareZeroMap.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.ideal_square_le_kernel_of_square_zero_map : ∀ (R Q B : Type) [CommRing R] [CommRing Q] [CommRing B] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ U), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → e.ker ^ 2 ≤ y.ker := by
  first | exact @GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker | exact GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker | (intros; apply GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker <;> assumption)
