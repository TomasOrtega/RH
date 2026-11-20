import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexPolyGradingFiniteExact
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
/- English proof (citation)
Apply `GlobalTheory.cubeComplex_polyGrading_finite_exact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCoherentCohomologyProofs%2FCubeComplexPolyGradingFiniteExact.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.finite_homology_and_exact_cubeComplex_polyGrading : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), (∀ p, Module.Finite R ((cubeComplex (grCube ι (polyGrading ι R) n)).homology p)) ∧ (1 ≤ n → ∀ p, (cubeComplex (grCube ι (polyGrading ι R) n)).ExactAt p) := by
  first | exact @GlobalTheory.cubeComplex_polyGrading_finite_exact | exact GlobalTheory.cubeComplex_polyGrading_finite_exact | (intros; apply GlobalTheory.cubeComplex_polyGrading_finite_exact <;> assumption)
