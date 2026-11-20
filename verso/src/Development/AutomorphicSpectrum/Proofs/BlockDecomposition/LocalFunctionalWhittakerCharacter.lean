import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LFPsi

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def tv (a y z : F) (x : Fin 2 → F) : Fin 2 → F := ![y + x 0 - a * (z + x 1), z + x 1]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [blk, uni, uni2, tv, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring`.
-/
theorem blk_mul_uni (a y z : F) (x : Fin 2 → F) :
    blk x * ((uni a y z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((uni2 a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * blk (tv a y z x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, uni, uni2, tv, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

def tvEquiv (a y z : F) : (Fin 2 → F) ≃ᵐ (Fin 2 → F) where
  toFun := tv a y z
  invFun x := ![x 0 + a * x 1 - y, x 1 - z]
  left_inv x := by
    ext i; fin_cases i <;> simp [tv]
  right_inv x := by
    ext i; fin_cases i <;> simp [tv]
  measurable_toFun := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · simp only [tv]
      exact (Continuous.measurable (by fun_prop) : Measurable fun x : Fin 2 → F => y + x 0 - a * (z + x 1))
    · simp only [tv]
      exact (Continuous.measurable (by fun_prop) : Measurable fun x : Fin 2 → F => z + x 1)
  measurable_invFun := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact (Continuous.measurable (by fun_prop) : Measurable fun x : Fin 2 → F => x 0 + a * x 1 - y)
    · exact (Continuous.measurable (by fun_prop) : Measurable fun x : Fin 2 → F => x 1 - z)

/- English proof (translation)
Use `set μ := selfDualMeasure ψ with hμ`. Establish `e : MeasurePreserving (MeasurableEquiv.piFinTwo fun _ : Fin 2 => F) (vol2 ψ) (μ.prod μ)` using `measurePreserving_piFinTwo (fun _ => μ)`. Establish `Q : MeasurePreserving (fun p : F × F => (z + p.1, y + p.2 - a * (z + p.1))) (μ.prod μ) (μ.prod μ)`. Use `MeasurePreserving.skew_product (f := fun t => z + t) (g := fun t s => y + s - a * (z + t)) (measurePreserving_add_left μ z) ?_ ?_` and prove the remaining obligations. Conclude with `Continuous.measurable (by unfold Function.uncurry; fun_prop)`.

Use `Filter.Eventually.of_forall fun t => ?_` and prove the remaining obligations. Establish `: (fun s => y + s - a * (z + t)) = fun s => s + (y - a * (z + t))`. Use extensionality with `s`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `(measurePreserving_add_right μ _).map_eq`. Establish `sw : MeasurePreserving (Prod.swap : F × F → F × F) (μ.prod μ) (μ.prod μ)` using `Measure.measurePreserving_swap`. Establish `all` using `(MeasurePreserving.symm _ e).comp (sw.comp (Q.comp (sw.comp e)))`. Use `all using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x i`.

Apply the tactic sequence `fin_cases i <;> simp [tv, MeasurableEquiv.piFinTwo]`.
-/
theorem mp_tv (ψ : AddChar F Circle) (a y z : F) :
    MeasurePreserving (tv a y z) (vol2 ψ) (vol2 ψ) := by
  set μ := selfDualMeasure ψ with hμ
  have e : MeasurePreserving (MeasurableEquiv.piFinTwo fun _ : Fin 2 => F) (vol2 ψ) (μ.prod μ) :=
    measurePreserving_piFinTwo (fun _ => μ)
  have Q : MeasurePreserving (fun p : F × F => (z + p.1, y + p.2 - a * (z + p.1)))
      (μ.prod μ) (μ.prod μ) := by
    refine MeasurePreserving.skew_product (f := fun t => z + t)
      (g := fun t s => y + s - a * (z + t)) (measurePreserving_add_left μ z) ?_ ?_
    · exact Continuous.measurable (by unfold Function.uncurry; fun_prop)
    · refine Filter.Eventually.of_forall fun t => ?_
      have : (fun s => y + s - a * (z + t)) = fun s => s + (y - a * (z + t)) := by
        ext s; ring
      rw [this]
      exact (measurePreserving_add_right μ _).map_eq
  have sw : MeasurePreserving (Prod.swap : F × F → F × F) (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap
  have all := (MeasurePreserving.symm _ e).comp (sw.comp (Q.comp (sw.comp e)))
  convert all using 1
  ext x i
  fin_cases i <;> simp [tv, MeasurableEquiv.piFinTwo]

/- English proof (translation)
Unfold `inn`. Rewrite using `[← (mp_tv ψ a y z).integral_comp (tvEquiv a y z).measurableEmbedding (fun x => Φ (((h * uni2 a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * blk x * (g : Matrix (Fin 3) (Fin 3) F)) * (ψ (-x 1) : ℂ)), ← MeasureTheory.integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `hm : ((h : Matrix (Fin 2) (Fin 2) F)) * blk x * (((uni a y z * g : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) = (((h * uni2 a : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * blk (tv a y z x) * (g : Matrix (Fin 3) (Fin 3) F)`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.mul_assoc (h : Matrix (Fin 2) (Fin 2) F) (blk x), ← Matrix.mul_assoc (blk x), blk_mul_uni]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `hc : (ψ (-x 1) : ℂ) = (ψ z : ℂ) * (ψ (-(tv a y z x 1)) : ℂ)`. Establish `: -x 1 = z + -(tv a y z x 1)` using `by simp [tv]`. Rewrite using `[this, AddChar.map_add_eq_mul, Circle.coe_mul]`. Use `beta_reduce`.

Rewrite using `[hm, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inn_uni (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h : GL (Fin 2) F)
    (a y z : F) (g : GL (Fin 3) F) :
    inn ψ Φ h (uni a y z * g) = (ψ z : ℂ) * inn ψ Φ (h * uni2 a) g := by
  unfold inn
  rw [← (mp_tv ψ a y z).integral_comp (tvEquiv a y z).measurableEmbedding
      (fun x => Φ (((h * uni2 a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * blk x *
        (g : Matrix (Fin 3) (Fin 3) F)) * (ψ (-x 1) : ℂ)),
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hm : ((h : Matrix (Fin 2) (Fin 2) F)) * blk x *
        (((uni a y z * g : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      (((h * uni2 a : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * blk (tv a y z x) *
        (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc (h : Matrix (Fin 2) (Fin 2) F) (blk x),
      ← Matrix.mul_assoc (blk x), blk_mul_uni]
    simp only [Matrix.mul_assoc]
  have hc : (ψ (-x 1) : ℂ) = (ψ z : ℂ) * (ψ (-(tv a y z x 1)) : ℂ) := by
    have : -x 1 = z + -(tv a y z x 1) := by simp [tv]
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]
  beta_reduce
  rw [hm, hc]
  ring

/- English proof (translation)
Use `ext`. Simplify using `[uni, Matrix.det_fin_three]`.
-/
theorem det_uni (a y z : F) : GeneralLinearGroup.det (uni a y z : GL (Fin 3) F) = 1 := by
  ext
  simp [uni, Matrix.det_fin_three]

/- English proof (translation)
Use `ext`. Simplify using `[uni2, Matrix.det_fin_two]`.
-/
theorem det_unipotent_adele (a : F) : GeneralLinearGroup.det (uni2 a : GL (Fin 2) F) = 1 := by
  ext
  simp [uni2, Matrix.det_fin_two]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [uni2]`.
-/
theorem unipotent_inv_eq_neg (a : F) : (uni2 a : GL (Fin 2) F)⁻¹ = uni2 (-a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2]

/- English proof (translation)
Unfold `Wp`. Establish `hd : GeneralLinearGroup.det (uni a y z * g) = GeneralLinearGroup.det g`. Rewrite using `[map_mul, det_uni, one_mul]`. Use `set G : GL (Fin 2) F → ℂ := fun h => W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h g with hG'`. Establish `hi : ∀ h : GL (Fin 2) F, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h (uni a y z * g) = ((ψ a : ℂ) * (ψ z : ℂ)) * G (h * uni2 a)`.

Introduce `h`. Establish `h1 : W' (h * uni2 a)⁻¹ = (ψ (-a) : ℂ) * W' h⁻¹`. Rewrite using `[_root_.mul_inv_rev, unipotent_inv_eq_neg, hpsi]`. Establish `h2 : (ψ a : ℂ) * (ψ (-a) : ℂ) = 1`. Rewrite using `[← Circle.coe_mul, ← AddChar.map_add_eq_mul]`.

Simplify using the standard rewrite rules. Establish `h3 : GeneralLinearGroup.det (h * uni2 a) = GeneralLinearGroup.det h`. Rewrite using `[map_mul, det_unipotent_adele, mul_one]`. Simplify using `only [hG', h1, h3, inn_uni]`. Take the linear combination `(-(W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * (ψ z : ℂ) * inn ψ Φ (h * uni2 a) g)) * h2`.

Use `haveI : (hG ψ).IsMulRightInvariant := by`. Unfold `hG`. Use `infer_instance`. Simplify using `only [hi, hd]`. Rewrite using `[MeasureTheory.integral_const_mul, integral_mul_right_eq_self G (uni2 a), AddChar.map_add_eq_mul, Circle.coe_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem wp_uni (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ)
    (hpsi : ∀ x g, W' (uni2 x * g) = (ψ x : ℂ) * W' g) (a y z : F) (g : GL (Fin 3) F) :
    Wp ψ W' Φ (uni a y z * g) = (ψ (a + z) : ℂ) * Wp ψ W' Φ g := by
  unfold Wp
  have hd : GeneralLinearGroup.det (uni a y z * g) = GeneralLinearGroup.det g := by
    rw [map_mul, det_uni, one_mul]
  set G : GL (Fin 2) F → ℂ := fun h =>
    W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h g with hG'
  have hi : ∀ h : GL (Fin 2) F,
      W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h (uni a y z * g) =
        ((ψ a : ℂ) * (ψ z : ℂ)) * G (h * uni2 a) := by
    intro h
    have h1 : W' (h * uni2 a)⁻¹ = (ψ (-a) : ℂ) * W' h⁻¹ := by
      rw [_root_.mul_inv_rev, unipotent_inv_eq_neg, hpsi]
    have h2 : (ψ a : ℂ) * (ψ (-a) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      simp
    have h3 : GeneralLinearGroup.det (h * uni2 a) = GeneralLinearGroup.det h := by
      rw [map_mul, det_unipotent_adele, mul_one]
    simp only [hG', h1, h3, inn_uni]
    linear_combination (-(W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * (ψ z : ℂ) *
      inn ψ Φ (h * uni2 a) g)) * h2
  haveI : (hG ψ).IsMulRightInvariant := by
    unfold hG
    infer_instance
  simp only [hi, hd]
  rw [MeasureTheory.integral_const_mul, integral_mul_right_eq_self G (uni2 a),
    AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ ν W' Φ hyp x y z g`. Take `⟨-, -, ⟨V', hV, hW⟩, -⟩` from `hyp`. Conclude with `wp_uni ψ W' Φ (hV.psi W' hW) x y z g`.
-/
theorem sPsiW : SPsiW := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hyp x y z g
  obtain ⟨-, -, ⟨V', hV, hW⟩, -⟩ := hyp
  exact wp_uni ψ W' Φ (hV.psi W' hW) x y z g

end GlobalTheory.CompanionTheory.LFPsi
