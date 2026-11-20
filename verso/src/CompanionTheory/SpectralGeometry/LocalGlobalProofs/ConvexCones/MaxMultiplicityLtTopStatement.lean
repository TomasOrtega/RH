import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MaxMultiplicityLtTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaxSimplicialCellMultiplicityLtTopOfIsPolyFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FConvexCones%2FMaxMultiplicityLtTop.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.max_multiplicity_lt_top : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O), IsPolyFan bar q φ → maxMult bar q φ < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite.maxMult_lt_top | exact GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite.maxMult_lt_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite.maxMult_lt_top <;> assumption)
