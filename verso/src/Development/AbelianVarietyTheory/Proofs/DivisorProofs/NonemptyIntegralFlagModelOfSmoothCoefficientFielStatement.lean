import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIntegralFlagModelOfSmoothCoefficientFiel
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptyIntegralFlagModelOfSmoothCoefficientFiel.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.nonempty_integralFlagModel_of_smooth_coefficientField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → PushInvertible Y.t.G Y.t.PP.L → Nonempty (GlobalTheory.FlagMod.FlagModel Y) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.nonempty_flagModel | exact GlobalTheory.FlagMod.FieldFlag.nonempty_flagModel | (intros; apply GlobalTheory.FlagMod.FieldFlag.nonempty_flagModel <;> assumption)
