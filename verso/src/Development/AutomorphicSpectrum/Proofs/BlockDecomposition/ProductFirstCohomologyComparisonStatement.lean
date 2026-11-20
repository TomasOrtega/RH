import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFirstCohomologyComparison
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.USt
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Axis.exists_boxSys` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProductFirstCohomologyComparison.lean&line=304#L304)
-/
theorem _root_.GlobalTheory.T.product_first_cohomology_comparison : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (P : Type) [SemilatticeInf P] (S : Sys A.left P),
    ∃ (Q : Type) (_ : SemilatticeInf Q) (S' : Sys (A ⊗ A).left Q)
      (m : CoefMap (RingHom.id R) (box (OSys A.hom S)) (OSys (A ⊗ A).hom S')),
      Function.Surjective m.pull1 ∧
      (∀ x c, IsPullO (wOver (fst A A)) x c →
        (resSys _ S').pull1 c = m.pull1 ((boxL _).pull1 ((resSys _ S).pull1 x))) ∧
      (∀ x c, IsPullO (wOver (snd A A)) x c →
        (resSys _ S').pull1 c = m.pull1 ((boxR _).pull1 ((resSys _ S).pull1 x))) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_boxSys | exact GlobalTheory.CompanionTheory.Axis.exists_boxSys | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_boxSys <;> assumption)
