import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeAddMem
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FConvexCones%2FPsdConeAddMem.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.psd_cone_add_mem : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B ∈ psdCone bar X → B' ∈ psdCone bar X → B + B' ∈ psdCone bar X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone | exact GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone <;> assumption)
