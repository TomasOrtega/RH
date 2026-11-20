import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFarSet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SemiAbFibre.irreducibleSpace_fibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIrreducibleSpaceFibreSemiAbelianFieldPoint.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint : ∀ (T : Scheme.{0}) (G : Over T) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T), IrreducibleSpace (pullback G.hom x : Scheme.{0}) := by
  first | exact @GlobalTheory.SemiAbFibre.irreducibleSpace_fibre | exact GlobalTheory.SemiAbFibre.irreducibleSpace_fibre | (intros; apply GlobalTheory.SemiAbFibre.irreducibleSpace_fibre <;> assumption)
