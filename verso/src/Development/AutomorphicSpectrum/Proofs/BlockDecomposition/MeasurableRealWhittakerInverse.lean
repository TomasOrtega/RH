import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.GodementWeight

open Ad3.LR

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem measurable_det_of : Measurable (fun h : M22 => (Matrix.of h).det) := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem measurable_inv_entry (i j : Fin 2) :
    Measurable (fun h : M22 => ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  have hd : Measurable (fun h : M22 => ((Matrix.of h).det)⁻¹) := measurable_det_of.inv
  have key : (fun h : M22 => ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) i j) =
      fun h : M22 => ((Matrix.of h).det)⁻¹ * (Matrix.adjugate (Matrix.of h)) i j := by
    funext h
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [key]
  refine hd.mul ?_
  simp only [Matrix.adjugate_fin_two, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem measurable_det_inv :
    Measurable (fun h : M22 => ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det) := by
  simp only [Matrix.det_fin_two]
  exact ((measurable_inv_entry 0 0).mul (measurable_inv_entry 1 1)).sub
    ((measurable_inv_entry 0 1).mul (measurable_inv_entry 1 0))

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem measurable_sg {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun a => sg (f a)) := by
  unfold sg
  exact Measurable.ite (hf measurableSet_Iio) measurable_const measurable_const

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem measurable_Wm_inv (k : ℕ) :
    Measurable (fun h : M22 => Wm k ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hD := measurable_det_inv
  have e : ∀ i j : Fin 2, Measurable
      (fun h : M22 => ((((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) i j : ℝ) : ℂ)) :=
    fun i j => Complex.measurable_ofReal.comp (measurable_inv_entry i j)
  unfold Wm
  refine Measurable.ite (measurableSet_lt measurable_const hD) ?_ measurable_const
  have hden := (e 1 1).sub ((e 1 0).mul_const Complex.I)
  have hnum := (e 0 1).sub ((e 0 0).mul_const Complex.I)
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · exact Complex.measurable_ofReal.comp (hD.pow_const _)
  · exact hden.pow_const _
  · exact Complex.measurable_exp.comp ((hnum.div hden).const_mul _)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem measurable_weight (k : ℕ) :
    Measurable (fun h : M22 => Wm k (Matrix.of h)⁻¹ * sg (Matrix.of h).det *
      ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)) := by
  refine ((measurable_Wm_inv k).mul (measurable_sg measurable_det_of)).mul ?_
  exact Complex.measurable_ofReal.comp (measurable_det_of.abs.pow_const _)

end GlobalTheory.CompanionTheory.GodementWeight

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GlobalTheory.CompanionTheory.GodementWeight.main : ∀ k : ℕ, Measurable (fun h : Ad3.LR.M22 => Ad3.LR.Wm k (Matrix.of h)⁻¹ * Ad3.LR.sg (Matrix.of h).det * ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)) :=
  GlobalTheory.CompanionTheory.GodementWeight.measurable_weight
