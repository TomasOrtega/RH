import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.EmRCont

/- English proof (translation)
Establish `hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0`. Establish `h0 : h.val.det ≠ 0` using `(Matrix.isUnits_det_units h).ne_zero`. Rewrite `h0` using `[Matrix.det_fin_two]`. Rewrite using `[Matrix.det_fin_three]`. Simplify using the standard rewrite rules.

Introduce `hh`. Apply `h0` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `GL2LocalData.emR`. Rewrite using `[dif_pos hd]`.

Both sides reduce to the same expression.
-/
theorem val_emR (h : GL (Fin 2) ℝ) :
    ((GL2LocalData.emR h : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := by
  have hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 := by
    have h0 : h.val.det ≠ 0 := (Matrix.isUnits_det_units h).ne_zero
    rw [Matrix.det_fin_two] at h0
    rw [Matrix.det_fin_three]
    simp
    intro hh
    apply h0
    linarith
  unfold GL2LocalData.emR
  rw [dif_pos hd]
  rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, val_emR, val_emR, val_emR]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Units.val_mul]`.
-/
theorem emR_mul (g h : GL (Fin 2) ℝ) : GL2LocalData.emR (g * h) = GL2LocalData.emR g * GL2LocalData.emR h := by
  apply Units.ext
  rw [Units.val_mul, val_emR, val_emR, val_emR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Units.val_mul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[val_emR]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
theorem emR_one : GL2LocalData.emR (1 : GL (Fin 2) ℝ) = 1 := by
  apply Units.ext
  rw [val_emR]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
The claim follows from `eq_inv_of_mul_eq_one_left (by rw [← emR_mul, inv_mul_cancel, emR_one])`.
-/
theorem emR_inv (g : GL (Fin 2) ℝ) : GL2LocalData.emR g⁻¹ = (GL2LocalData.emR g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← emR_mul, inv_mul_cancel, emR_one])

/- English proof (translation)
Establish `c : ∀ i j, Continuous fun h : GL (Fin 2) ℝ => h.val i j` using `fun i j => Units.continuous_val.matrix_elem i j`. Establish `e : (fun h : GL (Fin 2) ℝ => (GL2LocalData.emR h).val) = fun h => !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1]` using `funext val_emR`. Rewrite using `[e]`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> first | exact c _ _ | exact continuous_const`.
-/
theorem continuous_emR_val : Continuous fun h : GL (Fin 2) ℝ => (GL2LocalData.emR h).val := by
  have c : ∀ i j, Continuous fun h : GL (Fin 2) ℝ => h.val i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have e : (fun h : GL (Fin 2) ℝ => (GL2LocalData.emR h).val) = fun h =>
      !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := funext val_emR
  rw [e]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> first | exact c _ _ | exact continuous_const

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨continuous_emR_val, ?_⟩` and prove the remaining obligations. Establish `e : (fun h : GL (Fin 2) ℝ => (((GL2LocalData.emR h)⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)) = (fun h : GL (Fin 2) ℝ => (GL2LocalData.emR h).val) ∘ fun h => h⁻¹`. Use function extensionality and compare the values at `h`. Simplify using `only [Function.comp, emR_inv]`. Rewrite using `[e]`.

Conclude with `continuous_emR_val.comp continuous_inv`.
-/
theorem continuous_emR : Continuous GL2LocalData.emR := by
  refine Units.continuous_iff.2 ⟨continuous_emR_val, ?_⟩
  have e : (fun h : GL (Fin 2) ℝ => (((GL2LocalData.emR h)⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)) =
      (fun h : GL (Fin 2) ℝ => (GL2LocalData.emR h).val) ∘ fun h => h⁻¹ := by
    funext h
    simp only [Function.comp, emR_inv]
  rw [e]
  exact continuous_emR_val.comp continuous_inv

end GlobalTheory.CompanionTheory.GL2Factorization.EmRCont
