import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsGlobalConditions
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GenFan.PhiOrder.isPhiDiv_comb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FToricChartsGlobalConditions.lean&line=205#L205)
-/
theorem _root_.GlobalTheory.T.toric_charts_global_conditions : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (φ : InvFun (𝓞 E)), IsPolFan H.bar (min D.p D.q) φ → NoSelfInt H.bar (min D.p D.q) φ → ∀ (Y : Model Xo c (RingHom.id c.F)) (BD : GlobalTheory.EffCartierData Y.X) (d : ℕ), SmoothOfRelativeDimension D.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) → (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) → IsPhiDiv (comb 0 φ d φ) Y BD := by
  first | exact @GlobalTheory.GenFan.PhiOrder.isPhiDiv_comb | exact GlobalTheory.GenFan.PhiOrder.isPhiDiv_comb | (intros; apply GlobalTheory.GenFan.PhiOrder.isPhiDiv_comb <;> assumption)
