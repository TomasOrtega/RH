import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapFlatSemiabelian
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FPowerMapFlatSemiabelian.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.power_map_flat_semiabelian : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N → Flat ((𝟙 G) ^ N).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian | exact GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian <;> assumption)
