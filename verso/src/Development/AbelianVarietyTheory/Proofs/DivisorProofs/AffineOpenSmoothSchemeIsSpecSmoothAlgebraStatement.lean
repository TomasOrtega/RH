import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenSmoothSchemeIsSpecSmoothAlgebra
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.affineChart_smooth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAffineOpenSmoothSchemeIsSpecSmoothAlgebra.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.affineOpen_smoothScheme_isSpec_smoothAlgebra : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)), Smooth Y.hom → ∀ (W : Y.left.Opens), IsAffineOpen W → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (k : Sp O ⟶ Y.left) (_ : IsOpenImmersion k), k.opensRange = W ∧ k ≫ Y.hom = spMap (algebraMap R O) ∧ Algebra.Smooth R O := by
  first | exact @GlobalTheory.Mum.affineChart_smooth | exact GlobalTheory.Mum.affineChart_smooth | (intros; apply GlobalTheory.Mum.affineChart_smooth <;> assumption)
