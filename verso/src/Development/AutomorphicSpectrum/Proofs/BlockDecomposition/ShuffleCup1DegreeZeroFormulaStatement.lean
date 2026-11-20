import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1DegreeZeroFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HopfC.shuffle_cup1_degree_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FShuffleCup1DegreeZeroFormula.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.shuffle_cup1_degree_zero_formula : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (u : Cn (box F) 1) (w : Cn (box F) 0), Sh F 0 (cup1 (box F) 0 u w) = bv F OrderHom.id (cst 1 0) u * bv F (cst 0 1) OrderHom.id w := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.shuffle_cup1_degree_zero | exact GlobalTheory.CompanionTheory.HopfC.shuffle_cup1_degree_zero | (intros; apply GlobalTheory.CompanionTheory.HopfC.shuffle_cup1_degree_zero <;> assumption)
