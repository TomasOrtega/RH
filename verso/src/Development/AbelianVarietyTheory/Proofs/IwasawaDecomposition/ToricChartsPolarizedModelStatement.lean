import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsPolarizedModel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FanTheta.isLB_detOm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FToricChartsPolarizedModel.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.toric_charts_polarized_model : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (BD : GlobalTheory.EffCartierData Y.X) (d : ℕ), 1 ≤ D.p + D.q → SmoothOfRelativeDimension D.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) → (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) → (GlobalTheory.FlagMod.detOm Y).IsLB := by
  first | exact @GlobalTheory.FanTheta.isLB_detOm | exact GlobalTheory.FanTheta.isLB_detOm | (intros; apply GlobalTheory.FanTheta.isLB_detOm <;> assumption)
