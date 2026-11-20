import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
open AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaNormal.hasTheta_of_smooth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasFibrewiseNonvanishingThetaSectionOfSmoothMode.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.hasFibrewiseNonvanishingThetaSection_of_smooth_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L := by
  first | exact @GlobalTheory.ThetaNormal.hasTheta_of_smooth | exact GlobalTheory.ThetaNormal.hasTheta_of_smooth | (intros; apply GlobalTheory.ThetaNormal.hasTheta_of_smooth <;> assumption)
