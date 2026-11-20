import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnit
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FTorsionGroupEtaleOfUnit.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.torsion_group_etale_of_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit | exact GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit <;> assumption)
