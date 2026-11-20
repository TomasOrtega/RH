import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalCoverResiduePoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteNormalCoverResiduePoint.lean&line=167#L167)
-/
theorem _root_.GlobalTheory.T.exists_finite_normal_cover_residue_point : ∀ (F : Type) [Field F] [CharZero F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) [LocallyOfFiniteType p] [QuasiCompact p] (y₀ : Y) (k' : Type) [Field k'] [Algebra (Y.residueField y₀) k'] [FiniteDimensional (Y.residueField y₀) k'], ∃ (W : Scheme.{0}) (_ : IsIntegral W) (π : W ⟶ Y) (j : Sp k' ⟶ W), IsFinite π ∧ AlgebraicGeometry.IsNoetherian W ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme W ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap (Y.residueField y₀) k') ≫ Y.fromSpecResidueField y₀ := by
  first | exact @GlobalTheory.ResidueCover.exists_normal_finite_cover | exact GlobalTheory.ResidueCover.exists_normal_finite_cover | (intros; apply GlobalTheory.ResidueCover.exists_normal_finite_cover <;> assumption)
