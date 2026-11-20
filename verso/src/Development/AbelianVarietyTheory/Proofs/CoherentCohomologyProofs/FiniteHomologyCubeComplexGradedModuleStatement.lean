import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteHomologyCubeComplexGradedModule
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCoherentCohomologyProofs%2FFiniteHomologyCubeComplexGradedModule.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.finite_homology_cubeComplex_gradedModule : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∀ n p, Module.Finite R ((cubeComplex (grCube ι ℳ n)).homology p) := by
  first | exact @GlobalTheory.finite_cubeComplex_grCube_homology | exact GlobalTheory.finite_cubeComplex_grCube_homology | (intros; apply GlobalTheory.finite_cubeComplex_grCube_homology <;> assumption)
