import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2

section Base
variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Unfold `q4`. Use `fun_prop`.
-/
theorem continuous_quaternaryQuadraticForm (δ : F) : Continuous (q4 δ) := by unfold q4; fun_prop

def tr2 (δ : F) (v : V4 F) : A F := v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)
end Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)

/- English proof (translation)
Simplify using `[nu]`.
-/
@[simp] theorem nu_one : nu F (1 : GL (Fin 2) (A E)) = 1 := by simp [nu]
/- English proof (translation)
Simplify using `[nu]`.
-/
theorem nu_mul (h h' : GL (Fin 2) (A E)) : nu F (h * h') = nu F h * nu F h' := by simp [nu]
/- English proof (translation)
Rewrite using `[nu, det_gl, map_one]`.
-/
@[simp] theorem nu_gl (g : G1 E) : nu F (gl g) = 1 := by rw [nu, det_gl, map_one]
/- English proof (translation)
Rewrite using `[nu, det_aE]`.
-/
@[simp] theorem nu_aE (a : (A E)ˣ) : nu F (aE a) = ideleNorm F E a := by rw [nu, det_aE]
/- English proof (translation)
Rewrite using `[nu, det_dM]`.
-/
@[simp] theorem nu_dM (a : (A E)ˣ) : nu F (dM a) = ideleNorm F E a := by rw [nu, det_dM]
/- English proof (translation)
Rewrite using `[nu, det_scalar, map_pow]`.
-/
theorem nu_scalar (z : (A E)ˣ) : nu F (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = ideleNorm F E z ^ 2 := by
  rw [nu, det_scalar, map_pow]
/- English proof (translation)
The claim follows from `continuous_ideleNorm.comp continuous_adelicGL2_det`.
-/
theorem continuous_nu : Continuous (nu F : GL (Fin 2) (A E) → (A F)ˣ) := continuous_ideleNorm.comp continuous_adelicGL2_det

namespace Dat

def star2 (X : Matrix (Fin 2) (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E) := (X.map D.bar)ᵀ
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjTransposeGal_apply (X : Matrix (Fin 2) (Fin 2) (A E)) (i j : Fin 2) : D.star2 X i j = D.bar (X j i) := rfl
/- English proof (translation)
Rewrite using `[star2, Matrix.map_mul, Matrix.transpose_mul]`. Both sides reduce to the same expression.
-/
theorem conjTransposeGal_mul (X Y : Matrix (Fin 2) (Fin 2) (A E)) : D.star2 (X * Y) = D.star2 Y * D.star2 X := by
  rw [star2, Matrix.map_mul, Matrix.transpose_mul]; rfl
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[conjTransposeGal_apply]`.
-/
@[simp] theorem conjTransposeGal_involutive (X : Matrix (Fin 2) (Fin 2) (A E)) : D.star2 (D.star2 X) = X := by ext i j; simp [conjTransposeGal_apply]
/- English proof (translation)
Rewrite using `[star2, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`.
-/
@[simp] theorem conjTransposeGal_one : D.star2 1 = 1 := by rw [star2, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
/- English proof (translation)
Rewrite using `[star2, Matrix.det_transpose, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_star2 (X : Matrix (Fin 2) (Fin 2) (A E)) : (D.star2 X).det = D.bar X.det := by
  rw [star2, Matrix.det_transpose, RingHom.map_det]; rfl
/- English proof (translation)
Simplify using `[herm, bar_mkE]`.
-/
theorem herm_eq (v : V4 F) : D.herm v = !![am E (v 1), D.mkE (v 2) (v 3); D.bar (D.mkE (v 2) (v 3)), am E (v 0)] := by
  simp [herm, bar_mkE]
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [conjTransposeGal_apply, herm_eq]`.
-/
@[simp] theorem conjTranspose_herm (v : V4 F) : D.star2 (D.herm v) = D.herm v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [conjTransposeGal_apply, herm_eq]
/- English proof (translation)
Apply the tactic sequence `ext i; fin_cases i <;> simp [unherm, herm_eq]`.
-/
@[simp] theorem unherm_herm (v : V4 F) : D.unherm (D.herm v) = v := by
  ext i; fin_cases i <;> simp [unherm, herm_eq]
/- English proof (translation)
Establish `h : ∀ i j, D.bar (X j i) = X i j` using `fun i j => congrFun (congrFun hX i) j`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [unherm, herm_eq]`. Use `exacts [(D.eq_am_of_bar_eq (h 0 0)).symm, h 1 0, (D.eq_am_of_bar_eq (h 1 1)).symm]`.
-/
theorem herm_unherm {X : Matrix (Fin 2) (Fin 2) (A E)} (hX : D.star2 X = X) : D.herm (D.unherm X) = X := by
  have h : ∀ i j, D.bar (X j i) = X i j := fun i j => congrFun (congrFun hX i) j
  ext i j; fin_cases i <;> fin_cases j <;> simp [unherm, herm_eq]
  exacts [(D.eq_am_of_bar_eq (h 0 0)).symm, h 1 0, (D.eq_am_of_bar_eq (h 1 1)).symm]
/- English proof (translation)
The claim follows from `Function.LeftInverse.injective D.unherm_herm`.
-/
theorem herm_injective : Function.Injective D.herm := Function.LeftInverse.injective D.unherm_herm
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [herm_eq, mkE_add]`.
-/
theorem herm_add (v v' : V4 F) : D.herm (v + v') = D.herm v + D.herm v' := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [herm_eq, mkE_add]
/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [herm_eq, ← am_mul_mkE]`.
-/
theorem herm_smul (a : A F) (v : V4 F) : D.herm (a • v) = am E a • D.herm v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [herm_eq, ← am_mul_mkE]
/- English proof (translation)
Rewrite using `[herm_eq, Matrix.det_fin_two_of, mkE_mul_bar, q4]`. Simplify using `only [map_sub, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_herm (v : V4 F) : (D.herm v).det = -am E (q4 D.δ v) := by
  rw [herm_eq, Matrix.det_fin_two_of, mkE_mul_bar, q4]; simp only [map_sub, map_mul]; ring
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem act_def (h : GL (Fin 2) (A E)) (v : V4 F) : D.act h v = D.unherm (h.val * D.herm v * D.star2 h.val) := rfl
/- English proof (translation)
The claim follows from `(congrArg D.herm (D.act_def h v)).trans <| D.herm_unherm (by rw [conjTransposeGal_mul, conjTransposeGal_mul, conjTransposeGal_involutive, conjTranspose_herm, Matrix.mul_assoc])`.
-/
theorem herm_act (h : GL (Fin 2) (A E)) (v : V4 F) : D.herm (D.act h v) = h.val * D.herm v * D.star2 h.val :=
  (congrArg D.herm (D.act_def h v)).trans <| D.herm_unherm (by rw [conjTransposeGal_mul, conjTransposeGal_mul, conjTransposeGal_involutive, conjTranspose_herm, Matrix.mul_assoc])
/- English proof (translation)
The claim follows from `D.herm_injective (by rw [herm_act]; simp)`.
-/
@[simp] theorem act_one (v : V4 F) : D.act 1 v = v := D.herm_injective (by rw [herm_act]; simp)
/- English proof (translation)
The claim follows from `D.herm_injective (by simp only [herm_act, Units.val_mul, conjTransposeGal_mul, Matrix.mul_assoc])`.
-/
theorem act_mul (h h' : GL (Fin 2) (A E)) (v : V4 F) : D.act (h * h') v = D.act h (D.act h' v) :=
  D.herm_injective (by simp only [herm_act, Units.val_mul, conjTransposeGal_mul, Matrix.mul_assoc])
/- English proof (translation)
Rewrite using `[← act_mul]`. Simplify using the standard rewrite rules.
-/
@[simp] theorem act_inv_act (h : GL (Fin 2) (A E)) (v : V4 F) : D.act h⁻¹ (D.act h v) = v := by rw [← act_mul]; simp
/- English proof (translation)
Rewrite using `[← act_mul]`. Simplify using the standard rewrite rules.
-/
@[simp] theorem act_act_inv (h : GL (Fin 2) (A E)) (v : V4 F) : D.act h (D.act h⁻¹ v) = v := by rw [← act_mul]; simp
/- English proof (translation)
The claim follows from `D.herm_injective (by simp only [herm_act, herm_add, Matrix.mul_add, Matrix.add_mul])`.
-/
theorem act_add (h : GL (Fin 2) (A E)) (v v' : V4 F) : D.act h (v + v') = D.act h v + D.act h v' :=
  D.herm_injective (by simp only [herm_act, herm_add, Matrix.mul_add, Matrix.add_mul])
/- English proof (translation)
The claim follows from `D.herm_injective (by simp only [herm_act, herm_smul, Matrix.mul_smul, Matrix.smul_mul])`.
-/
theorem act_smul (h : GL (Fin 2) (A E)) (a : A F) (v : V4 F) : D.act h (a • v) = a • D.act h v :=
  D.herm_injective (by simp only [herm_act, herm_smul, Matrix.mul_smul, Matrix.smul_mul])
/- English proof (translation)
The claim follows from `continuous_matrix fun i j => by have e : ∀ k l, Continuous fun v : V4 F => D.mkE (v k) (v l) := fun k l => D.continuous_mkE' (continuous_apply k) (continuous_apply l) simp only [herm_eq] fin_cases i <;> fin_cases j exacts [continuous_am.comp (continuous_apply 1), e 2 3, D.continu …`.
-/
theorem continuous_herm : Continuous D.herm := continuous_matrix fun i j => by
  have e : ∀ k l, Continuous fun v : V4 F => D.mkE (v k) (v l) := fun k l =>
    D.continuous_mkE' (continuous_apply k) (continuous_apply l)
  simp only [herm_eq]
  fin_cases i <;> fin_cases j
  exacts [continuous_am.comp (continuous_apply 1), e 2 3, D.continuous_bar.comp (e 2 3), continuous_am.comp (continuous_apply 0)]
/- English proof (translation)
The claim follows from `continuous_pi fun i => by have e : ∀ k l m, Continuous fun X : Matrix (Fin 2) (Fin 2) (A E) => D.co (X k l) m := fun k l m => (continuous_apply m).comp (D.continuous_co.comp ((continuous_apply l).comp (continuous_apply k))) fin_cases i exacts [e 1 1 0, e 0 0 0, e 0 1 0, e 0 1 1]`.
-/
theorem continuous_unherm : Continuous D.unherm := continuous_pi fun i => by
  have e : ∀ k l m, Continuous fun X : Matrix (Fin 2) (Fin 2) (A E) => D.co (X k l) m := fun k l m =>
    (continuous_apply m).comp (D.continuous_co.comp ((continuous_apply l).comp (continuous_apply k)))
  fin_cases i
  exacts [e 1 1 0, e 0 0 0, e 0 1 0, e 0 1 1]
/- English proof (translation)
Establish `h : Continuous fun p : GL (Fin 2) (A E) × V4 F => p.1.val` using `Units.continuous_val.comp continuous_fst`. Conclude with `D.continuous_unherm.comp ((h.matrix_mul (D.continuous_herm.comp continuous_snd)).matrix_mul (h.matrix_map D.continuous_bar).matrix_transpose)`.
-/
theorem continuous_act : Continuous fun p : GL (Fin 2) (A E) × V4 F => D.act p.1 p.2 := by
  have h : Continuous fun p : GL (Fin 2) (A E) × V4 F => p.1.val := Units.continuous_val.comp continuous_fst
  exact D.continuous_unherm.comp ((h.matrix_mul (D.continuous_herm.comp continuous_snd)).matrix_mul
    (h.matrix_map D.continuous_bar).matrix_transpose)
/- English proof (translation)
Establish `e : (fun x => D.act (h x) (v x)) = (fun p : GL (Fin 2) (A E) × V4 F => D.act p.1 p.2) ∘ fun x => (h x, v x)` using `rfl`. Rewrite using `[e]`. Conclude with `D.continuous_act.comp (hh.prodMk hv)`.
-/
theorem continuous_act' {X : Type*} [TopologicalSpace X] {h : X → GL (Fin 2) (A E)} {v : X → V4 F} (hh : Continuous h)
    (hv : Continuous v) : Continuous fun x => D.act (h x) (v x) := by
  have e : (fun x => D.act (h x) (v x)) = (fun p : GL (Fin 2) (A E) × V4 F => D.act p.1 p.2) ∘ fun x => (h x, v x) := rfl
  rw [e]; exact D.continuous_act.comp (hh.prodMk hv)

def actL : GL (Fin 2) (A E) →* (V4 F ≃ₗ[A F] V4 F) where
  toFun h :=
    { toFun := D.act h, invFun := D.act h⁻¹, left_inv := D.act_inv_act h, right_inv := D.act_act_inv h
      map_add' := D.act_add h, map_smul' := D.act_smul h }
  map_one' := LinearEquiv.ext D.act_one
  map_mul' h h' := LinearEquiv.ext (D.act_mul h h')
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem actL_apply (h : GL (Fin 2) (A E)) (v : V4 F) : D.actL h v = D.act h v := rfl

def actT (h : GL (Fin 2) (A E)) : V4 F ≃ₜ+ V4 F where
  toFun := D.act h
  invFun := D.act h⁻¹
  left_inv := D.act_inv_act h
  right_inv := D.act_act_inv h
  map_add' := D.act_add h
  continuous_toFun := D.continuous_act' continuous_const continuous_id
  continuous_invFun := D.continuous_act' continuous_const continuous_id
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem actT_apply (h : GL (Fin 2) (A E)) (v : V4 F) : D.actT h v = D.act h v := rfl

def actM (h : GL (Fin 2) (A E)) : Matrix (Fin 4) (Fin 4) (A F) := Matrix.of fun i j => D.act h (Pi.single j 1) i
/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix'_apply]`. Both sides reduce to the same expression.
-/
theorem actM_eq (h : GL (Fin 2) (A E)) : D.actM h = LinearMap.toMatrix' (D.actL h).toLinearMap := by
  ext i j; rw [LinearMap.toMatrix'_apply]; rfl
/- English proof (translation)
Rewrite using `[actM_eq, LinearMap.toMatrix'_mulVec]`. Both sides reduce to the same expression.
-/
theorem actM_mulVec (h : GL (Fin 2) (A E)) (v : V4 F) : D.actM h *ᵥ v = D.act h v := by
  rw [actM_eq, LinearMap.toMatrix'_mulVec]; rfl
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[actM, Matrix.one_apply, Pi.single_apply]`.
-/
theorem actM_one : D.actM 1 = 1 := by ext i j; simp [actM, Matrix.one_apply, Pi.single_apply]
/- English proof (translation)
Rewrite using `[actM_eq, actM_eq, actM_eq, ← LinearMap.toMatrix'_mul, map_mul]`. Both sides reduce to the same expression.
-/
theorem actM_mul (h h' : GL (Fin 2) (A E)) : D.actM (h * h') = D.actM h * D.actM h' := by
  rw [actM_eq, actM_eq, actM_eq, ← LinearMap.toMatrix'_mul, map_mul]; rfl

def actG : GL (Fin 2) (A E) →* GL (Fin 4) (A F) :=
  MonoidHom.toHomUnits { toFun := D.actM, map_one' := D.actM_one, map_mul' := D.actM_mul }
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem actG_val (h : GL (Fin 2) (A E)) : (D.actG h).val = D.actM h := rfl

/- English proof (translation)
Establish `e` using `congrArg Matrix.det (D.herm_act h v)`. Rewrite `e` using `[Matrix.det_mul, Matrix.det_mul, det_herm, det_herm, det_star2]`. Apply `am_injective (E := E)` to reduce the goal to its premises. Rewrite using `[map_mul, nu, D.am_ideleNorm, Matrix.GeneralLinearGroup.val_det_apply]`. Take the linear combination `-e`.
-/
theorem quadForm_act (h : GL (Fin 2) (A E)) (v : V4 F) : q4 D.δ (D.act h v) = (nu F h : (A F)ˣ) * q4 D.δ v := by
  have e := congrArg Matrix.det (D.herm_act h v)
  rw [Matrix.det_mul, Matrix.det_mul, det_herm, det_herm, det_star2] at e
  apply am_injective (E := E)
  rw [map_mul, nu, D.am_ideleNorm, Matrix.GeneralLinearGroup.val_det_apply]
  linear_combination -e

/- English proof (translation)
Apply `D.herm_injective` to reduce the goal to its premises. Rewrite using `[herm_act]`. Establish `hθ` using `D.rt_θ_sq`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [herm, conjTransposeGal_apply, Matrix.mul_apply, Fin.sum_univ_two, bar_mkE, mkE_def, bar_rt, D.conj, ← hθ, map_ofNat] <;> ring`.
-/
theorem act_nU (u t : A F) (v : V4 F) : D.act (gl (nU (D.mkE u t))) v =
    ![v 0, v 1 + 2 * (u * v 2 - rt D.δ * (t * v 3)) + (u ^ 2 - rt D.δ * t ^ 2) * v 0, v 2 + u * v 0, v 3 + t * v 0] := by
  apply D.herm_injective
  rw [herm_act]
  have hθ := D.rt_θ_sq
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [herm, conjTransposeGal_apply, Matrix.mul_apply, Fin.sum_univ_two, bar_mkE, mkE_def, bar_rt, D.conj, ← hθ, map_ofNat] <;> ring
/- English proof (translation)
Apply `D.herm_injective` to reduce the goal to its premises. Rewrite using `[herm_act, herm_smul, D.am_ideleNorm]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [conjTransposeGal_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring`.
-/
theorem act_scalar (z : (A E)ˣ) (v : V4 F) :
    D.act (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = ((ideleNorm F E z : (A F)ˣ) : A F) • v := by
  apply D.herm_injective
  rw [herm_act, herm_smul, D.am_ideleNorm]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjTransposeGal_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end Dat

end UpperTheory.ConvolutionTheory.R2

end
