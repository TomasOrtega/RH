import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGrpLawAgreesWithAbelianSchemeLaw
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChartGrpLawAgreesWithAbelianSchemeLaw.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.chart_grpLaw_agrees_with_abelian_scheme_law : ∀ (σ : Setup) (E : Emb σ) (x : Sp σ.R), MulAgree (σ.C x).G σ.A (E.emb x) E.ιA := by
  first | exact @GlobalTheory.Desc.ChartLaw.chart_mulAgree | exact GlobalTheory.Desc.ChartLaw.chart_mulAgree | (intros; apply GlobalTheory.Desc.ChartLaw.chart_mulAgree <;> assumption)
