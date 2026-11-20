import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSpecAffineOpenFunctionsBijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDualNumberSpecAffineOpenFunctionsBijective.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.dualNumberSpec_affineOpen_functions_bijective : ∀ (O : Type) [CommRing O] (V : (Sp O).Opens), IsAffineOpen V → Function.Bijective (fun ab : Γ(Sp O, V) × Γ(Sp O, V) => (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.1 + (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.2 * resG _ le_top (epsFn O)) := by
  first | exact @GlobalTheory.LieVB.bijective_add_mul_epsFn | exact GlobalTheory.LieVB.bijective_add_mul_epsFn | (intros; apply GlobalTheory.LieVB.bijective_add_mul_epsFn <;> assumption)
