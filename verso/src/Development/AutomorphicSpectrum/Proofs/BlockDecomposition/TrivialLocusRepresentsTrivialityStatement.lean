import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusRepresentsTriviality
import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TrivPull.triv_pull_iff` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTrivialLocusRepresentsTriviality.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.trivial_locus_represents_triviality : ∀ {S : Scheme.{0}} (A Y Z : Over S) (N : LB (A ⊗ Y).left), N.IsLB → ∀ (i : Z ⟶ Y), PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i → ∀ (T : Over S) (y : T ⟶ Y) {B : Scheme.{0}} (b : B ⟶ T.left), Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b)) ↔ ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
  first | exact @GlobalTheory.CompanionTheory.TrivPull.triv_pull_iff | exact GlobalTheory.CompanionTheory.TrivPull.triv_pull_iff | (intros; apply GlobalTheory.CompanionTheory.TrivPull.triv_pull_iff <;> assumption)
