import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstants
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
Apply `GlobalTheory.GermConst.germ_constFn_origin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGermOriginConstantSectionEqOriginStalkConstants.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (O : G.left.Opens) (hO : origin G ∈ O) (r : R), (G.left.presheaf.germ O (origin G) hO).hom (constFn G.hom O r) = constO G r := by
  first | exact @GlobalTheory.GermConst.germ_constFn_origin | exact GlobalTheory.GermConst.germ_constFn_origin | (intros; apply GlobalTheory.GermConst.germ_constFn_origin <;> assumption)
