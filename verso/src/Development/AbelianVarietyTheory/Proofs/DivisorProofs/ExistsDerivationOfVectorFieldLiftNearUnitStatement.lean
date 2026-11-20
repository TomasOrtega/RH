import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationOfVectorFieldLiftNearUnit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDerivationOfVectorFieldLiftNearUnit.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.exists_derivation_of_vectorFieldLift_near_unit : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ D' : Derivation ℤ R R, ∀ r, D' r = D r := by
  first | exact @GlobalTheory.Heat.liftDer_isDerivation | exact GlobalTheory.Heat.liftDer_isDerivation | (intros; apply GlobalTheory.Heat.liftDer_isDerivation <;> assumption)
