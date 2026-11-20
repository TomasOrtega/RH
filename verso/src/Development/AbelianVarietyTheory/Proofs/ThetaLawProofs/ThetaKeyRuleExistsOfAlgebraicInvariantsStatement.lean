import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleExistsOfAlgebraicInvariants
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KeyHouse.keyRule_of_kaSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FThetaKeyRuleExistsOfAlgebraicInvariants.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.thetaKeyRule_exists_of_algebraic_invariants : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → KaSt → KeyDesc → ∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf := by
  first | exact @GlobalTheory.KeyHouse.keyRule_of_kaSt | exact GlobalTheory.KeyHouse.keyRule_of_kaSt | (intros; apply GlobalTheory.KeyHouse.keyRule_of_kaSt <;> assumption)
