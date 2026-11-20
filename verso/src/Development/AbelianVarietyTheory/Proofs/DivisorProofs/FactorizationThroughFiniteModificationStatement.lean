import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorizationThroughFiniteModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.finite_modif_eq_gp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFactorizationThroughFiniteModification.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.factorization_through_finite_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h → M'.gp ≫ h = M.gp → ∀ (Z : Scheme.{0}) (a : Z ⟶ M'.S) (c : Z ⟶ Sp (FractionRing R)), a ≫ h = c ≫ M.gp → a = c ≫ M'.gp := by
  first | exact @GlobalTheory.Mum.finite_modif_eq_gp | exact GlobalTheory.Mum.finite_modif_eq_gp | (intros; apply GlobalTheory.Mum.finite_modif_eq_gp <;> assumption)
