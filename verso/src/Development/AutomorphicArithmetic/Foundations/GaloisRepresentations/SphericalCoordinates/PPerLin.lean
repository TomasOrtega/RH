import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwining

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Introduce `O _ bar g ρ D P P' H hP hH hc hP'`. Establish `hdet : LinearMap.det (Matrix.toLin' H) ≠ 0` using `by rwa [LinearMap.det_toLin']`. Set `h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)` to `LinearMap.equivOfDetNeZero _ hdet`. Establish `happ : ∀ z, h z = H *ᵥ z` using `fun z => rfl`. Establish `key` using `IsPeriod.comp_linearEquiv O bar D g ρ ρ P h hP (fun a z => by`.

Rewrite using `[happ, happ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc])`. Establish `hEq : P' = (↑h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).toAddMonoidHom.comp P`. Use extensionality with `x`. Simplify using `[hP', happ]`. Rewrite using `[hEq]`.

Conclude with `key`.
-/
theorem UpperTheory.Gal.W2.perLin_of :
    UpperTheory.Gal.W2.PerLin := by
  intro O _ bar g ρ D P P' H hP hH hc hP'
  have hdet : LinearMap.det (Matrix.toLin' H) ≠ 0 := by rwa [LinearMap.det_toLin']
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearMap.equivOfDetNeZero _ hdet
  have happ : ∀ z, h z = H *ᵥ z := fun z => rfl
  have key := IsPeriod.comp_linearEquiv O bar D g ρ ρ P h hP (fun a z => by
    rw [happ, happ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc])
  have hEq : P' = (↑h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).toAddMonoidHom.comp P := by
    ext x
    simp [hP', happ]
  rw [hEq]
  exact key
