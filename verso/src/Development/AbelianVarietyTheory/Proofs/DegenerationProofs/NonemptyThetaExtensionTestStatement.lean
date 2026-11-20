import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyThetaExtensionTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
/- English proof (citation)
Apply `GlobalTheory.ZJ.Core.Theta.nonempty_ext` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FNonemptyThetaExtensionTest.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.nonempty_thetaExtension_test : Semi.extend_existsSt.{0} → ∀ (C : Core) (T : C.Theta) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.TestCart → Nonempty (T.Ext τ) := by
  first | exact @GlobalTheory.ZJ.Core.Theta.nonempty_ext | exact GlobalTheory.ZJ.Core.Theta.nonempty_ext | (intros; apply GlobalTheory.ZJ.Core.Theta.nonempty_ext <;> assumption)
