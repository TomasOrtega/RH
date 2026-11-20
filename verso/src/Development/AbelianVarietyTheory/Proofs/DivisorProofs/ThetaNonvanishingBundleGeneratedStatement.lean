import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundleStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaNonvanishingBundleGenerated.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.theta_nonvanishing_bundle_generated : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M : LB A.left), M.IsLB → ∀ (g : ℕ) (u : HolUnif A M g) (θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ →
    (∀ z, θ z ≠ 0) →
    (∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) →
    HasGen M := by
  first | exact @GlobalTheory.HolUnifSec.hasGen_of_periodic | exact GlobalTheory.HolUnifSec.hasGen_of_periodic | (intros; apply GlobalTheory.HolUnifSec.hasGen_of_periodic <;> assumption)
