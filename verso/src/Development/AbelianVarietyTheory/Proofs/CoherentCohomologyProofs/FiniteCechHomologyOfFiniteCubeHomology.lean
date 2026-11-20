import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexAcyclicIffQuasiIsoCechAug

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hex : (ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (K.toCycles_comp_homologyπ i j)).Exact` using `ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hij)`. Rewrite `hex` using `[ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]`. Conclude with `Module.Finite.of_exact hex ((ModuleCat.epi_iff_surjective (K.homologyπ j)).1 inferInstance)`.
-/
theorem finite_cycles_of_finite_homology {R : Type} [Ring R] {α : Type} {c : ComplexShape α}
    (K : HomologicalComplex (ModuleCat.{0} R) c) (i j : α) (hij : c.prev j = i)
    [Module.Finite R (K.X i)] [Module.Finite R (K.homology j)] :
    Module.Finite R (K.cycles j) := by
  have hex : (ShortComplex.mk (K.toCycles i j) (K.homologyπ j)
      (K.toCycles_comp_homologyπ i j)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hij)
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex
  exact Module.Finite.of_exact hex
    ((ModuleCat.epi_iff_surjective (K.homologyπ j)).1 inferInstance)

/- English proof (translation)
Consider the cases of `p with`. Consider the case `zero`. Establish `h1` using `h 1`. Establish `h2 : Module.Finite R ((cubeComplex A).X 0)` using `Module.Finite.equiv (Cube.termZeroEquiv A).symm`. Establish `h3` using `finite_cycles_of_finite_homology (cubeComplex A) 0 1 (by simp)`.

Conclude with `Module.Finite.equiv (cubeCyclesIso A 1 ≪≫ (cechHomologyZeroIso A).symm).toLinearEquiv`. Consider the case `succ p`. Establish `h1` using `h (p + 2)`. Conclude with `Module.Finite.equiv (cechHomologySuccIso A p).symm.toLinearEquiv`.
-/
theorem finite_cechHomology_of_finite_cubeHomology (ι : Type) [LinearOrder ι] (R : Type)
    [CommRing R] [IsNoetherianRing R] (A : Cube.{0} ι R) (h₀ : Module.Finite R (A.obj ∅))
    (h : ∀ p, Module.Finite R ((cubeComplex A).homology p)) (p : ℕ) :
    Module.Finite R ((cechComplex A).homology p) := by
  cases p with
  | zero =>
    have h1 := h 1
    have h2 : Module.Finite R ((cubeComplex A).X 0) :=
      Module.Finite.equiv (Cube.termZeroEquiv A).symm
    have h3 := finite_cycles_of_finite_homology (cubeComplex A) 0 1 (by simp)
    exact Module.Finite.equiv
      (cubeCyclesIso A 1 ≪≫ (cechHomologyZeroIso A).symm).toLinearEquiv
  | succ p =>
    have h1 := h (p + 2)
    exact Module.Finite.equiv (cechHomologySuccIso A p).symm.toLinearEquiv

end GlobalTheory
