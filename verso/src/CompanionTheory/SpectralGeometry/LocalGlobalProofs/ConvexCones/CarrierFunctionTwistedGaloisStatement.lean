import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierFunctionTwistedGalois
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FConvexCones%2FCarrierFunctionTwistedGalois.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.carrier_function_twisted_galois : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (ψ : InvFun O), IsTwG w0 ψ → IsTwG w0 (carFun bar ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun | exact GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun <;> assumption)
