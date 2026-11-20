import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFieldExtCancel
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.spMap_field_cancel` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpMapFieldExtCancel.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.spMap_field_ext_cancel : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (io : Ω →+* Ω') (X : Scheme.{0}) (a b : Sp Ω ⟶ X), spMap io ≫ a = spMap io ≫ b → a = b := by
  first | exact @GlobalTheory.Mum.spMap_field_cancel | exact GlobalTheory.Mum.spMap_field_cancel | (intros; apply GlobalTheory.Mum.spMap_field_cancel <;> assumption)
