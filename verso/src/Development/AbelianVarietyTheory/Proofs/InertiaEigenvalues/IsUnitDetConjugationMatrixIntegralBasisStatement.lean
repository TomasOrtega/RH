import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetConjugationMatrixIntegralBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.Unr.conj_matrix_det_isUnit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsUnitDetConjugationMatrixIntegralBasis.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isUnit_det_conjugationMatrix_integralBasis : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), (∀ x, φ (K.c x) = K'.c (φ x)) → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det := by
  first | exact @GlobalTheory.UnitLemma.Unr.conj_matrix_det_isUnit | exact GlobalTheory.UnitLemma.Unr.conj_matrix_det_isUnit | (intros; apply GlobalTheory.UnitLemma.Unr.conj_matrix_det_isUnit <;> assumption)
