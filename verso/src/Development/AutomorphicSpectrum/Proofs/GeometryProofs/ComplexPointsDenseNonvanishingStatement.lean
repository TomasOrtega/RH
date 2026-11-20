import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishing
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FComplexPointsDenseNonvanishing.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.complex_points_dense_nonvanishing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense | exact GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense <;> assumption)
