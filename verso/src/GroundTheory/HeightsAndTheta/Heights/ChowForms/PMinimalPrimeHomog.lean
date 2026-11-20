import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i r hr`. Use `h r hr i using 1` and compare the differences between its conclusion and the goal. Conclude with `decomposition.decompose'_apply r i`. Introduce `h f hf d`.

Conclude with `homogeneousComponent_mem_of_mem h hf d`.
-/
theorem isHomogIdeal_iff_isHomogeneous_degree {R : Type*} [CommRing R] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  constructor
  · intro h i r hr
    convert h r hr i using 1
    exact decomposition.decompose'_apply r i
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d

/- English proof (translation)
Introduce `F _ n J W hJ hW`. Rewrite `hJ`, the goal using `[isHomogIdeal_iff_isHomogeneous_degree]`. Establish `hWp : W.IsPrime` using `hW.1.1`. Establish `hcore : (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal = W`. Apply `le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)` to reduce the goal to its premises.

Use `hW.2 ⟨hWp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)` and prove the remaining obligations. Conclude with `hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)`. Rewrite using `[← hcore]`. Conclude with `(W.homogeneousCore _).isHomogeneous`.
-/
theorem MinimalPrimeHomog.proof : MinimalPrimeHomog.Statement := by
  intro F _ n J W hJ hW
  rw [isHomogIdeal_iff_isHomogeneous_degree] at hJ ⊢
  have hWp : W.IsPrime := hW.1.1
  have hcore : (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal = W := by
    apply le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
    refine hW.2 ⟨hWp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    exact hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  rw [← hcore]
  exact (W.homogeneousCore _).isHomogeneous

end GroundTheory.Heights₂.Heights
