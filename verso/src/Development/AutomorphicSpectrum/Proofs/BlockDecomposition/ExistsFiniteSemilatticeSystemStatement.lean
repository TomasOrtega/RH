import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSemilatticeSystem
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
Apply `GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsFiniteSemilatticeSystem.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_finite_semilattice_system : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s → QuasiCompact s →
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact | exact GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact <;> assumption)
