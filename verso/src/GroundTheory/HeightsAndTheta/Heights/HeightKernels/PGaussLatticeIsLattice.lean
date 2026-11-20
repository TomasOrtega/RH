import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PGaussLatticeIsLattice

def colBasis {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    Module.Basis (Fin g) ℝ (EuclideanSpace ℝ (Fin g)) :=
  (Pi.basisFun ℝ (Fin g)).map
    ((B.toLinearEquiv' (B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hB))).trans
      (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm)

/- English proof (translation)
Rewrite using `[colBasis, Module.Basis.map_apply, Pi.basisFun_apply]`. Both sides reduce to the same expression.
-/
theorem colBasis_apply {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) (i : Fin g) :
    colBasis B hB i = WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  rw [colBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

/- English proof (translation)
Unfold `gaussLattice`. Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `(colBasis_apply B hB i).symm`.
-/
theorem gaussLattice_eq_span {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    gaussLattice B = Submodule.span ℤ (Set.range (colBasis B hB)) := by
  unfold gaussLattice
  congr 2
  funext i
  exact (colBasis_apply B hB i).symm

end PGaussLatticeIsLattice

open PGaussLatticeIsLattice in

/- English proof (translation)
Introduce `g B hB`. Establish `h` using `gaussLattice_eq_span B hB`. Use `⟨?_, fun {_} => ⟨?_⟩⟩` and prove the remaining obligations. Rewrite using `[h]`. Use `infer_instance`.

Rewrite using `[h]`. Conclude with `ZSpan.span_top (colBasis B hB)`.
-/
theorem GaussLatticeIsLattice.proof : GaussLatticeIsLattice.Statement := by
  intro g B hB
  have h := gaussLattice_eq_span B hB
  refine ⟨?_, fun {_} => ⟨?_⟩⟩
  · rw [h]; infer_instance
  · rw [h]; exact ZSpan.span_top (colBasis B hB)

end

end GroundTheory.Heights₂.Heights
