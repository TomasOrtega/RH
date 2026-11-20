import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.LtrFourier

noncomputable section

/- English proof (translation)
Establish `hmap` using `GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi (tInv (A⁻¹))`. Establish `hdet : Matrix.GeneralLinearGroup.det (tInv (A⁻¹)) = Matrix.GeneralLinearGroup.det A`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]`. Express the relevant statement in the definitionally equal form `(((A⁻¹)⁻¹ : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])ᵀ.det = _`.

Rewrite using `[Matrix.det_transpose, inv_inv]`. Establish `hfun : (fun x : Fin n → 𝔸[k] => x ᵥ* ((tInv (A⁻¹) : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])) = fun x => (A : Matrix (Fin n) (Fin n) 𝔸[k]) *ᵥ x`. Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `x ᵥ* (((A⁻¹)⁻¹ : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])ᵀ = _`. Rewrite using `[inv_inv]`.

Conclude with `Matrix.vecMul_transpose _ x`. Rewrite `hmap` using `[hdet, hfun]`. Then use the resulting hypothesis.
-/
theorem map_mulVec_fin {k : Type} [Field k] [NumberField k] {n : ℕ} (A : GL (Fin n) 𝔸[k]) :
    (adeleMeasurePi k).map (fun x : Fin n → 𝔸[k] => (A : Matrix (Fin n) (Fin n) 𝔸[k]) *ᵥ x) =
      ENNReal.ofReal ((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ •
        adeleMeasurePi k (ι := Fin n) := by
  have hmap := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi (tInv (A⁻¹))
  have hdet : Matrix.GeneralLinearGroup.det (tInv (A⁻¹)) = Matrix.GeneralLinearGroup.det A := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    change (((A⁻¹)⁻¹ : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])ᵀ.det = _
    rw [Matrix.det_transpose, inv_inv]
  have hfun : (fun x : Fin n → 𝔸[k] =>
      x ᵥ* ((tInv (A⁻¹) : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])) =
      fun x => (A : Matrix (Fin n) (Fin n) 𝔸[k]) *ᵥ x := by
    funext x
    change x ᵥ* (((A⁻¹)⁻¹ : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])ᵀ = _
    rw [inv_inv]
    exact Matrix.vecMul_transpose _ x
  rwa [hdet, hfun] at hmap

/- English proof (translation)
Use `set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι`. Set `P : GL (Fin (Fintype.card ι)) 𝔸[k]` to `⟨(A : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm, ((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm, by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv], by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]⟩`. Establish `hdet : Matrix.GeneralLinearGroup.det P = Matrix.GeneralLinearGroup.det A`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]`.

Conclude with `Matrix.det_submatrix_equiv_self _ _`. Establish `h1 : MeasurePreserving (fun x : ι → 𝔸[k] => x ∘ e.symm) (adeleMeasurePi k) (adeleMeasurePi k)` using `GroundTheory.Heights₂.Theta.measurePreserving_comp_equiv (adeleMeasure k) e.symm`. Establish `h3 : MeasurePreserving (fun x : Fin (Fintype.card ι) → 𝔸[k] => x ∘ e) (adeleMeasurePi k) (adeleMeasurePi k)` using `GroundTheory.Heights₂.Theta.measurePreserving_comp_equiv (adeleMeasure k) e`. Establish `hP : Measurable fun x : Fin (Fintype.card ι) → 𝔸[k] => (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝔸[k]) *ᵥ x` using `(continuous_const.matrix_mulVec continuous_id).measurable`. Establish `hfun : (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) = (fun x => x ∘ e) ∘ (fun x => (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝔸[k]) *ᵥ x) ∘ (fun x => x ∘ e.symm)`.

Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply]`. Express the relevant statement in the definitionally equal form `_ = ((A : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm *ᵥ (x ∘ e.symm)) ∘ e`. Establish `hx : (x ∘ e.symm) ∘ e = x`. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hx]`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[hfun, ← Measure.map_map h3.measurable (hP.comp h1.measurable), ← Measure.map_map hP h1.measurable, h1.map_eq, map_mulVec_fin P, hdet, Measure.map_smul, h3.map_eq]`.
-/
theorem map_mulVec {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : GL ι 𝔸[k]) :
    (adeleMeasurePi k).map (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) =
      ENNReal.ofReal ((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ •
        adeleMeasurePi k (ι := ι) := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let P : GL (Fin (Fintype.card ι)) 𝔸[k] :=
    ⟨(A : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm,
      ((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm,
      by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]⟩
  have hdet : Matrix.GeneralLinearGroup.det P = Matrix.GeneralLinearGroup.det A := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    exact Matrix.det_submatrix_equiv_self _ _
  have h1 : MeasurePreserving (fun x : ι → 𝔸[k] => x ∘ e.symm) (adeleMeasurePi k)
      (adeleMeasurePi k) := GroundTheory.Heights₂.Theta.measurePreserving_comp_equiv (adeleMeasure k) e.symm
  have h3 : MeasurePreserving (fun x : Fin (Fintype.card ι) → 𝔸[k] => x ∘ e) (adeleMeasurePi k)
      (adeleMeasurePi k) := GroundTheory.Heights₂.Theta.measurePreserving_comp_equiv (adeleMeasure k) e
  have hP : Measurable fun x : Fin (Fintype.card ι) → 𝔸[k] =>
      (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝔸[k]) *ᵥ x :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hfun : (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) =
      (fun x => x ∘ e) ∘
        (fun x => (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝔸[k]) *ᵥ x) ∘
          (fun x => x ∘ e.symm) := by
    funext x
    simp only [Function.comp_apply]
    change _ = ((A : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm *ᵥ (x ∘ e.symm)) ∘ e
    have hx : (x ∘ e.symm) ∘ e = x := by
      funext j
      simp
    rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hx]
    funext i
    simp
  rw [hfun, ← Measure.map_map h3.measurable (hP.comp h1.measurable),
    ← Measure.map_map hP h1.measurable, h1.map_eq, map_mulVec_fin P, hdet, Measure.map_smul,
    h3.map_eq]

def mulVecHomeo {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : GL ι 𝔸[k]) : (ι → 𝔸[k]) ≃ₜ (ι → 𝔸[k]) where
  toFun x := (A : Matrix ι ι 𝔸[k]) *ᵥ x
  invFun x := ((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ x
  left_inv x := by
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv x := by
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

/- English proof (translation)
Establish `hemb : MeasurableEmbedding (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x)` using `(mulVecHomeo A).measurableEmbedding`. Rewrite using `[← hemb.integral_map, map_mulVec, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 (ideleModule k (Matrix.GeneralLinearGroup.det A)).2.le), Complex.real_smul, Complex.ofReal_inv]`.
-/
theorem integral_comp_mulVec {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : GL ι 𝔸[k]) (f : (ι → 𝔸[k]) → ℂ) :
    ∫ x, f ((A : Matrix ι ι 𝔸[k]) *ᵥ x) ∂adeleMeasurePi k =
      (((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ : ℂ) *
        ∫ x, f x ∂adeleMeasurePi k := by
  have hemb : MeasurableEmbedding (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) :=
    (mulVecHomeo A).measurableEmbedding
  rw [← hemb.integral_map, map_mulVec, integral_smul_measure, ENNReal.toReal_ofReal
      (inv_nonneg.2 (ideleModule k (Matrix.GeneralLinearGroup.det A)).2.le),
    Complex.real_smul, Complex.ofReal_inv]

/- English proof (translation)
Introduce `k _ _ ι _ _ A F`. Use function extensionality and compare the values at `y`. Establish `h` using `integral_comp_mulVec A (fun z => F z * (adelicChar k (∑ i, (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) i * y i) : ℂ))`. Simplify using `only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h`. Establish `hp : ∀ z : ι → 𝔸[k], ∑ i, (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) i * y i = ∑ i, z i * (((tInv A : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ y) i`.

Introduce `z`. Express the relevant statement in the definitionally equal form `(((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) ⬝ᵥ y = z ⬝ᵥ ((((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]))ᵀ *ᵥ y)`. Rewrite using `[Matrix.mulVec_transpose, dotProduct_comm _ y, Matrix.dotProduct_mulVec, dotProduct_comm]`. Simplify using `only [hp] at h`. Simplify `h` using `only [adelicFourierPi, ltr, Pi.smul_apply, smul_eq_mul]`.
-/
theorem adelicFourierPi_ltr : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ), adelicFourierPi k (ltr A F) =
      (((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ : ℂ) •
        ltr (tInv A) (adelicFourierPi k F) := by
  intro k _ _ ι _ _ A F
  funext y
  have h := integral_comp_mulVec A (fun z => F z *
    (adelicChar k (∑ i, (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) i * y i) : ℂ))
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
  have hp : ∀ z : ι → 𝔸[k], ∑ i, (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) i * y i =
      ∑ i, z i * (((tInv A : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ y) i := by
    intro z
    change (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) ⬝ᵥ y =
      z ⬝ᵥ ((((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]))ᵀ *ᵥ y)
    rw [Matrix.mulVec_transpose, dotProduct_comm _ y, Matrix.dotProduct_mulVec,
      dotProduct_comm]
  simp only [hp] at h
  simpa only [adelicFourierPi, ltr, Pi.smul_apply, smul_eq_mul] using h

end

end GlobalTheory.CompanionTheory.LtrFourier
