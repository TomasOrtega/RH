import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarDepthTwistedGalois
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist.isTwG_starDepth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FConvexCones%2FStarDepthTwistedGalois.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.star_depth_twisted_galois : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (ψ w : InvFun O), IsTwG w0 ψ → IsTwG w0 w → IsTwG w0 (starDepth bar ψ w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist.isTwG_starDepth | exact GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist.isTwG_starDepth | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist.isTwG_starDepth <;> assumption)
