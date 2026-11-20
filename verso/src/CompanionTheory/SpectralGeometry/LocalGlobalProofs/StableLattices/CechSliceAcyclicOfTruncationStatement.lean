import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechSliceAcyclicOfTruncation
import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulHomologyEqZeroOfAcyclicFibre
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfPoints
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBGenericOfSpecial
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FCechSliceAcyclicOfTruncation.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.cech_slice_acyclic_of_truncation : ∀ {ν κ : Type} [LinearOrder ν] [LinearOrder κ] [Finite ν] [Finite κ] {R : Type} [CommRing R]
    (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R)
    (hA : ∀ t : Finset κ, 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A t)).Acyclic)
    (hT : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (GlobalTheory.Cube.trunc₂ A)).homology (n + 2))) (j : κ), (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A {j})).Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂ | exact GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂ | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂ <;> assumption)
