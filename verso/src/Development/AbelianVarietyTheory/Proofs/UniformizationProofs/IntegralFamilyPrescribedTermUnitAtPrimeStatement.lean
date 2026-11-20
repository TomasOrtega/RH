import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralFamilyPrescribedTermUnitAtPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
/- English proof (citation)
Apply `GlobalTheory.integralFamily_at_prime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FIntegralFamilyPrescribedTermUnitAtPrime.lean&line=363#L363)
-/
theorem _root_.GlobalTheory.T.integralFamily_prescribedTerm_unit_at_prime : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D.toPre W) → ∀ p : (Spec (CommRingCat.of R)), p ∈ W → ∀ (k : ℕ), 1 ≤ k → ∀ (ρ : D.toPre.X) (s : D.toPre.SecB k ρ), ∃ r : R, r ∉ p.asIdeal ∧ ∃ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ j, (f ρ).f j = resTop _ (scal D.toPre.P.A.hom r) * (s).f j) ∧ ∀ β, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (f β).f j = 0 := by
  first | exact @GlobalTheory.integralFamily_at_prime | exact GlobalTheory.integralFamily_at_prime | (intros; apply GlobalTheory.integralFamily_at_prime <;> assumption)
