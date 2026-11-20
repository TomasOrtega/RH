import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThFam.exists_intFam_lead` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIntegralThetaFamilyPrescribedLeadingTerm.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), (∀ α : D.toPre.X, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ b : D.toPre.SecB k α, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b) ∧ ∀ k : ℕ, 1 ≤ k → ∀ b : D.toPre.SecB k 0, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead 0 b := by
  first | exact @GlobalTheory.ThFam.exists_intFam_lead | exact GlobalTheory.ThFam.exists_intFam_lead | (intros; apply GlobalTheory.ThFam.exists_intFam_lead <;> assumption)
