import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.XSmulMemWeightedHomogeneousSubmodule

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `ι _ _ R _ M _ _ _ _ ℳ _ _ _ n`. Use `GradedHilbert.finite_piece (ι := ι) ℳ (fun i k m hm => ?_) n` and prove the remaining obligations. Use `grSMul_mem ℳ (X_mem_polyGrading i) hm` as an intermediate fact. Use `first`. Consider the case `exact this`.

Consider the case `exact add_comm k 1 ▸ this`. Consider the case `simpa [add_comm] using this`.
-/
theorem finite_piece_of_polyGradedSMul : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∀ n, Module.Finite R (ℳ n) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ _ n
  refine GradedHilbert.finite_piece (ι := ι) ℳ (fun i k m hm => ?_) n
  have := grSMul_mem ℳ (X_mem_polyGrading i) hm
  first
    | exact this
    | exact add_comm k 1 ▸ this
    | simpa [add_comm] using this

end GlobalTheory
