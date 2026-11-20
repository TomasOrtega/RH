import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RiemannLatticeOverPoint
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FRiemannLatticeOverPoint.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.riemann_lattice_over_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ), IsOver 𝔐 z κ p → FibreLat Xo.univ.t p R → FibreLat 𝔐.t z R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver <;> assumption)
