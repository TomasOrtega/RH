import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompSymm

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.SmIntHaar

open MeasureTheory

variable {k : Type} [Field k]

def glLinearEquiv {t : ℕ} (w : GL (Fin t) k) : (Fin t → k) ≃ₗ[k] (Fin t → k) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k))
    (Matrix.toLin' ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k))
    (by
      rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

/- English proof (translation)
Use function extensionality and compare the values at `v`. Both sides reduce to the same expression.
-/
theorem coe_glLinearEquiv_symm {t : ℕ} (w : GL (Fin t) k) :
    ((glLinearEquiv w).symm : (Fin t → k) → (Fin t → k)) =
      ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec := by
  funext v
  rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[LinearEquiv.coe_det]`. Use `show LinearMap.det (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k)) = _`. Rewrite using `[LinearMap.det_toLin']`. Both sides reduce to the same expression.
-/
theorem det_glLinearEquiv {t : ℕ} (w : GL (Fin t) k) :
    LinearEquiv.det (glLinearEquiv w) = Matrix.GeneralLinearGroup.det w := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  show LinearMap.det (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k)) = _
  rw [LinearMap.det_toLin']
  rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `borelize k`. Establish `hp : @BorelSpace (Fin t → k) _ MeasurableSpace.pi` using `Pi.borelSpace`. Establish `e : m = MeasurableSpace.pi` using `hb.measurable_eq.trans hp.measurable_eq.symm`. Substitute `e` using the available equality. Rewrite using `[← coe_glLinearEquiv_symm, ← det_glLinearEquiv]`.

Conclude with `GlobalTheory.ChangeVarPi.map_symm_eq_smul k (Fin t) μ (glLinearEquiv w)`.
-/
theorem map_inv_mulVec (t : ℕ) [m : MeasurableSpace (Fin t → k)] [hb : BorelSpace (Fin t → k)]
    (μ : Measure (Fin t → k)) [μ.IsAddHaarMeasure] (w : GL (Fin t) k) :
    μ.map ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ := by
  borelize k
  have hp : @BorelSpace (Fin t → k) _ MeasurableSpace.pi := Pi.borelSpace
  have e : m = MeasurableSpace.pi := hb.measurable_eq.trans hp.measurable_eq.symm
  subst e
  rw [← coe_glLinearEquiv_symm, ← det_glLinearEquiv]
  exact GlobalTheory.ChangeVarPi.map_symm_eq_smul k (Fin t) μ (glLinearEquiv w)

/- English proof (translation)
Introduce `k _ _ _ _ t _ _ μ _ Z _ _ w φ hl _`. Establish `hc : Continuous ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec` using `continuous_const.matrix_mulVec continuous_id`. Establish `hval : ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) = (((distribHaarChar k (Matrix.GeneralLinearGroup.det w) : NNReal) : ℝ) : ℂ)`. Rewrite using `[detChar_apply, val_absPow, Complex.cpow_one]`. Both sides reduce to the same expression.

Rewrite using `[hval]`. Unfold `smInt`. Rewrite using `[smul_finsum]`. Use `finsum_congr fun v => ?_` and prove the remaining obligations. Establish `hlev : μ ((fun x => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec x)) ⁻¹' {v}) = (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ (φ ⁻¹' {v})`.

Rewrite using `[← Measure.smul_apply, ← map_inv_mulVec t μ w]`. Conclude with `(Measure.map_apply hc.measurable (hl.isOpen_fiber v).measurableSet).symm`. Rewrite using `[hlev, ENNReal.toReal_smul, smul_smul, NNReal.smul_def, smul_eq_mul, Complex.ofReal_mul]`.
-/
theorem smInt_comp_inv_mulVec : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] {Z : Type} [AddCommGroup Z] [Module ℂ Z] (w : GL (Fin t) k) (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (fun v => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ φ := by
  intro k _ _ _ _ t _ _ μ _ Z _ _ w φ hl _
  have hc : Continuous ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec :=
    continuous_const.matrix_mulVec continuous_id
  have hval : ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) =
      (((distribHaarChar k (Matrix.GeneralLinearGroup.det w) : NNReal) : ℝ) : ℂ) := by
    rw [detChar_apply, val_absPow, Complex.cpow_one]
    rfl
  rw [hval]
  unfold smInt
  rw [smul_finsum]
  refine finsum_congr fun v => ?_
  have hlev : μ ((fun x => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec x)) ⁻¹' {v}) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ (φ ⁻¹' {v}) := by
    rw [← Measure.smul_apply, ← map_inv_mulVec t μ w]
    exact (Measure.map_apply hc.measurable (hl.isOpen_fiber v).measurableSet).symm
  rw [hlev, ENNReal.toReal_smul, smul_smul, NNReal.smul_def, smul_eq_mul, Complex.ofReal_mul]

end GlobalTheory.CompanionTheory.Rodier.SmIntHaar

end
