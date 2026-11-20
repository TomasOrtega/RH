import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.Conj.secTw_add_chart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPullbackThetaSectionsGaloisTwistChartAdd.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  first | exact @GlobalTheory.Mum.Conj.secTw_add_chart | exact GlobalTheory.Mum.Conj.secTw_add_chart | (intros; apply GlobalTheory.Mum.Conj.secTw_add_chart <;> assumption)
