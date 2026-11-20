import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoord
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.valF_psi_of_psiCoord` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPsiValueFractionRingOfPsiCoord.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.psi_value_fractionRing_of_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (r : R), Formalism.L2.Pj.PsiCoord D χ r → ∃ j : PUnit → D.P.L.ι, ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) ∧ valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  first | exact @GlobalTheory.Poinc.valF_psi_of_psiCoord | exact GlobalTheory.Poinc.valF_psi_of_psiCoord | (intros; apply GlobalTheory.Poinc.valF_psi_of_psiCoord <;> assumption)
