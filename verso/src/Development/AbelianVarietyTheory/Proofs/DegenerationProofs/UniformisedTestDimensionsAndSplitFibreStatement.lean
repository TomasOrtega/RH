import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FUniformisedTestDimensionsAndSplitFibre.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), u.A.g = S.g ∧ u.D.toPre.P.g + Module.finrank ℤ u.D.toPre.X = S.g ∧ SmoothOfRelativeDimension S.g u.G.hom ∧ 4 ≤ S.N ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField u.V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue u.V))).obj u.G) := by
  first | exact @GlobalTheory.ZH.utest_dim_and_split | exact GlobalTheory.ZH.utest_dim_and_split | (intros; apply GlobalTheory.ZH.utest_dim_and_split <;> assumption)
