import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
/- English proof (citation)
Apply `GlobalTheory.FamBaseChange.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FRingsOfIntegers%2FIntegralDegenerationFamilyBaseChangeExtensionFie.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.integralDegenerationFamily_baseChange_extensionField : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (k : ℕ) (E : Fam D.toPre (FractionRing R) k) (g : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ θ : Fam D.toPre F k, ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (θ.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre F).left 1 := by
  first | exact @GlobalTheory.FamBaseChange.main | exact GlobalTheory.FamBaseChange.main | (intros; apply GlobalTheory.FamBaseChange.main <;> assumption)
