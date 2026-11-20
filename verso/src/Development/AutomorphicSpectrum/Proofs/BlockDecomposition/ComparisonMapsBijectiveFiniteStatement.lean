import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonMapsBijectiveFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FComparisonMapsBijectiveFinite.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.comparison_maps_bijective_finite : ∀ (R S P : Type) [CommRing R] [CommRing S] [Algebra R S] [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧ Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.th_bijective | exact GlobalTheory.CompanionTheory.PerfVB.th_bijective | (intros; apply GlobalTheory.CompanionTheory.PerfVB.th_bijective <;> assumption)
