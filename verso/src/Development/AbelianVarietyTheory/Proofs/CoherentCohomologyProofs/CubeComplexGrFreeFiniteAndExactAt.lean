import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexPolyGradingFiniteExactStatement

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `ι _ _ R _ r d`. Use `⟨fun n p => ?_, 1 + ∑ k, |d k|, fun n hn p => ?_⟩` and prove the remaining obligations. Establish `h (k : Fin r) : Module.Finite R ((cubeComplex (grCube ι (grShift (polyGrading ι R) (-d k)) n)).homology p)`. Establish `: Module.Finite R (((cubeFunctor ι R).obj (grCube ι (polyGrading ι R) (n + -d k))).homology p)` using `(GlobalTheory.T.finite_homology_and_exact_cubeComplex_polyGrading ι R (n + -d k)).1 p`. Use the proof step `Module.Finite.equiv (HomologicalComplex.homologyMapIso ((cubeFunctor ι R).mapIso (grCubeShiftIso (polyGrading ι R) (-d k) n)) p).toLinearEquiv.symm`.

Conclude with `Module.Finite.equiv (cubeHomologyDirectSumEquiv (fun k => grCube ι (grShift (polyGrading ι R) (-d k)) n) p ≪≫ₗ (HomologicalComplex.homologyMapIso ((cubeFunctor ι R).mapIso (grCubePiIso ι (fun k => grShift (polyGrading ι R) (-d k)) n)) p).toLinearEquiv.symm)`. Use `(cubeComplex_grPi_exactAt_iff (fun k => grShift (polyGrading ι R) (-d k)) n p).2 fun k => ?_` and prove the remaining obligations. Establish `h₁ : |d k| ≤ ∑ k, |d k|` using `Finset.single_le_sum (f := fun k => |d k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)`. Establish `h₂` using `le_abs_self (d k)`. Conclude with `(exactAt_iff_of_quasiIsoAt ((cubeFunctor ι R).mapIso (grCubeShiftIso (polyGrading ι R) (-d k) n)).hom p).2 ((GlobalTheory.T.finite_homology_and_exact_cubeComplex_polyGrading ι R (n + -d k)).2 (by omega) p)`.
-/
theorem cubeComplex_grFree_finite_and_exactAt :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (r : ℕ) (d : Fin r → ℤ),
      (∀ n p, Module.Finite R ((cubeComplex (grCube ι (grFree ι R d) n)).homology p)) ∧
        ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, (cubeComplex (grCube ι (grFree ι R d) n)).ExactAt p := by
  intro ι _ _ R _ r d
  refine ⟨fun n p => ?_, 1 + ∑ k, |d k|, fun n hn p => ?_⟩
  · have h (k : Fin r) : Module.Finite R
        ((cubeComplex (grCube ι (grShift (polyGrading ι R) (-d k)) n)).homology p) :=
      have : Module.Finite R (((cubeFunctor ι R).obj
          (grCube ι (polyGrading ι R) (n + -d k))).homology p) :=
        (GlobalTheory.T.finite_homology_and_exact_cubeComplex_polyGrading ι R (n + -d k)).1 p
      Module.Finite.equiv (HomologicalComplex.homologyMapIso ((cubeFunctor ι R).mapIso
        (grCubeShiftIso (polyGrading ι R) (-d k) n)) p).toLinearEquiv.symm
    exact Module.Finite.equiv
      (cubeHomologyDirectSumEquiv (fun k => grCube ι (grShift (polyGrading ι R) (-d k)) n) p ≪≫ₗ
        (HomologicalComplex.homologyMapIso ((cubeFunctor ι R).mapIso
          (grCubePiIso ι (fun k => grShift (polyGrading ι R) (-d k)) n)) p).toLinearEquiv.symm)
  · refine (cubeComplex_grPi_exactAt_iff (fun k => grShift (polyGrading ι R) (-d k)) n p).2
      fun k => ?_
    have h₁ : |d k| ≤ ∑ k, |d k| :=
      Finset.single_le_sum (f := fun k => |d k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h₂ := le_abs_self (d k)
    exact (exactAt_iff_of_quasiIsoAt ((cubeFunctor ι R).mapIso
      (grCubeShiftIso (polyGrading ι R) (-d k) n)).hom p).2
      ((GlobalTheory.T.finite_homology_and_exact_cubeComplex_polyGrading ι R (n + -d k)).2 (by omega) p)

end GlobalTheory
