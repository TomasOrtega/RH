import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagSpaceComponentSmoothProjectiveConnected.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.flagSpace_component_smooth_projective_connected : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ T.X Z := by
  first | exact @GlobalTheory.VarFlag.isVariety₀_flag | exact GlobalTheory.VarFlag.isVariety₀_flag | (intros; apply GlobalTheory.VarFlag.isVariety₀_flag <;> assumption)
