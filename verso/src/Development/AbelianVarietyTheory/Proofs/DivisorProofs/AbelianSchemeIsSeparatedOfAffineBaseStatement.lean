import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.abelianScheme_left_isSeparated_of_affine` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianSchemeIsSeparatedOfAffineBase.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.abelianScheme_isSeparated_of_affine_base : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated := by
  first | exact @GlobalTheory.abelianScheme_left_isSeparated_of_affine | exact GlobalTheory.abelianScheme_left_isSeparated_of_affine | (intros; apply GlobalTheory.abelianScheme_left_isSeparated_of_affine <;> assumption)
