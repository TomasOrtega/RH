import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelSemiAbelianRelDimCotangentVectorBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModelSemiAbelianRelDimCotangentVectorBundle.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) Y.t.G.hom ∧ GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  first | exact @GlobalTheory.ModelRelDim.relDim_and_isVB_omega | exact GlobalTheory.ModelRelDim.relDim_and_isVB_omega | (intros; apply GlobalTheory.ModelRelDim.relDim_and_isVB_omega <;> assumption)
