import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralBasisUnramifiedInvolutionExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformizerCompatibleUnramifiedExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitTraceFormDiscrUnramifiedExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetConjugationMatrixIntegralBasisStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

/- English proof (translation)
Introduce `K K' d φ h hd`. Use `letI : Algebra K.E K'.E := φ.toAlgebra`. Take `⟨w, hw⟩` from `GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt K K' d φ h hd`. Use `⟨w, ?_⟩` and prove the remaining obligations. Take `⟨π, π', hππ, hm, hm'⟩` from `GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt K K' d φ h`.

Take `⟨u, hu, hue⟩` from `GlobalTheory.T.isUnit_traceForm_discr_unramifiedExt K K' d φ h π π' hππ hm hm' w hw`. Take `⟨v, hv, hve⟩` from `GlobalTheory.T.isUnit_det_conjugationMatrix_integralBasis K K' d φ h.2.1 w hw`. Establish `key : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))) = (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)) * (Matrix.of fun m l => w.repr (K'.c (w l)) m)`. Use extensionality with `k l`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`.

Use `conv_lhs => rw [← w.sum_repr (K'.c (w l))]`. Rewrite using `[Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_smul, smul_eq_mul, mul_comm]`. Establish `hdet : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = algebraMap K.O K.E (u * v)`.

Rewrite using `[key, Matrix.det_mul, ← hue, ← hve, map_mul]`. Rewrite using `[hdet]`. Use `⟨?_, GlobalTheory.UnitLemma.Orbit.val_unit _ (hu.mul hv)⟩` and prove the remaining obligations. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]`. Conclude with `(hu.mul hv).ne_zero`.
-/
theorem GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧ val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0 := by
  intro K K' d φ h hd
  letI : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt K K' d φ h hd
  refine ⟨w, ?_⟩
  obtain ⟨π, π', hππ, hm, hm'⟩ := GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt K K' d φ h
  obtain ⟨u, hu, hue⟩ := GlobalTheory.T.isUnit_traceForm_discr_unramifiedExt K K' d φ h π π' hππ hm hm' w hw
  obtain ⟨v, hv, hve⟩ := GlobalTheory.T.isUnit_det_conjugationMatrix_integralBasis K K' d φ h.2.1 w hw
  have key : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))) =
      (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)) * (Matrix.of fun m l => w.repr (K'.c (w l)) m) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.of_apply]
    conv_lhs => rw [← w.sum_repr (K'.c (w l))]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hdet : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = algebraMap K.O K.E (u * v) := by
    rw [key, Matrix.det_mul, ← hue, ← hve, map_mul]
  rw [hdet]
  refine ⟨?_, GlobalTheory.UnitLemma.Orbit.val_unit _ (hu.mul hv)⟩
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]
  exact (hu.mul hv).ne_zero
