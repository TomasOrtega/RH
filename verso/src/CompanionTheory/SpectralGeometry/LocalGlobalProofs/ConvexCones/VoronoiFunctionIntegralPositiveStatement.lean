import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFunctionIntegralPositive
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Fan.vorFun_int_pos` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FConvexCones%2FVoronoiFunctionIntegralPositive.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.voronoi_function_integral_positive : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank ℤ O * q ≤ g → Module.finrank O X ≤ q → (∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (vorFun O g).evalZ β = n) ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (vorFun O g).evalZ β := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.vorFun_int_pos | exact GlobalTheory.CompanionTheory.Ar.Fan.vorFun_int_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.vorFun_int_pos <;> assumption)
