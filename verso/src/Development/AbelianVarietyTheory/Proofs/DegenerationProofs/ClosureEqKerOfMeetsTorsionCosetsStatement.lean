import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureEqKerOfMeetsTorsionCosets
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FClosureEqKerOfMeetsTorsionCosets.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.closure_eq_ker_of_meets_torsion_cosets' : ∀ (I X : Type) [AddCommGroup X] [Module.Free ℤ X] (n J M : ℕ), n ≠ 0 → 2 ≤ J → M = n ^ J → ∀ (yy : (I → ZMod M) →+ X ⧸ (nsmulAddMonoidHom M : X →+ X).range), Function.Surjective yy → ∀ Z : Set (I → ZMod M), Z ⊆ yy.ker → (∀ a ∈ yy.ker, ∃ b, n • b = 0 ∧ a + b ∈ Z) → AddSubgroup.closure Z = yy.ker := by
  first | exact @GlobalTheory.closure_eq_ker_of_meets_torsion_cosets | exact GlobalTheory.closure_eq_ker_of_meets_torsion_cosets | (intros; apply GlobalTheory.closure_eq_ker_of_meets_torsion_cosets <;> assumption)
