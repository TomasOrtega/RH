import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightIdentity
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FRootOriginWeightIdentity.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.root_origin_weight_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → ∃ (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ j, (n₀ j : ℝ) = (Fx.kA * Fx.q' : ℕ) * RM.coef nu (-1) j) ∧ 0 < N₀ ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ∈ chartLatNm RM.y (combLine (RM.line 1) n₀).a 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model | exact GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model <;> assumption)
