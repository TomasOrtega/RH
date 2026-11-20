import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemRationalConeOfPerturbation
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FConvexCones%2FMemRationalConeOfPerturbation.lean&line=177#L177)
-/
theorem _root_.GlobalTheory.T.mem_rational_cone_of_perturbation : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ ε : ℝ, 0 < ε → B + ε • B₀ ∈ rcone γ) → B ∈ rcone γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg | exact GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg <;> assumption)
