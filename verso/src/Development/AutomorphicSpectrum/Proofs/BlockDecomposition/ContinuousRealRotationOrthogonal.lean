import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
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

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.OrthParam

/- English proof (translation)
Rewrite using `[Matrix.det_fin_two_of]`. Use `Real.sin_sq_add_cos_sq θ` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem rot_det_ne (θ : ℝ) : !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ].det ≠ 0 := by
  rw [Matrix.det_fin_two_of]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith

/- English proof (translation)
Simplify using `only [GL2LocalData.rotR, dif_pos (rot_det_ne θ)]`. Both sides reduce to the same expression.
-/
theorem rot_val (θ : ℝ) :
    (GL2LocalData.rotR θ : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  simp only [GL2LocalData.rotR, dif_pos (rot_det_ne θ)]
  rfl

/- English proof (translation)
Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[rot_val]`. Establish `h` using `Real.sin_sq_add_cos_sq θ`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith`.
-/
theorem rot_inv_val (θ : ℝ) :
    (((GL2LocalData.rotR θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [rot_val]
  have h := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: (Units.val ∘ GL2LocalData.rotR : ℝ → Matrix (Fin 2) (Fin 2) ℝ) = fun θ => !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]` using `funext rot_val`. Rewrite using `[this]`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> fun_prop`.

Establish `hc : Continuous fun θ : ℝ => (!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ)`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> fun_prop`. Conclude with `hc.congr fun θ => (rot_inv_val θ).symm`.
-/
theorem continuous_rot : Continuous GL2LocalData.rotR := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ GL2LocalData.rotR : ℝ → Matrix (Fin 2) (Fin 2) ℝ) =
        fun θ => !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := funext rot_val
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have hc : Continuous fun θ : ℝ =>
        (!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ) := by
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    exact hc.congr fun θ => (rot_inv_val θ).symm

/- English proof (translation)
Rewrite using `[rot_val]`. Establish `h` using `Real.sin_sq_add_cos_sq θ`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> nlinarith`.
-/
theorem rot_orth (θ : ℝ) : (GL2LocalData.rotR θ).val * (GL2LocalData.rotR θ).valᵀ = 1 := by
  rw [rot_val]
  have h := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> nlinarith

/- English proof (translation)
Introduce `ε`. Use `⟨?_, fun θ => ?_⟩` and prove the remaining obligations. Unfold `GL2LocalData.kR`. Conclude with `continuous_rot.mul continuous_const`. Establish `hr` using `rot_orth θ`.

Consider the cases of `ε`. Simplify `hr` using `[GL2LocalData.kR]`. Establish `hd : ((dg2 (1 : ℝˣ) (-1) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * ((dg2 (1 : ℝˣ) (-1) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`.

Simplify using `[dg2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]`. Simplify using `only [GL2LocalData.kR, if_true, Units.val_mul, Matrix.transpose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hd, Matrix.mul_one, hr]`.
-/
theorem kR_continuous_orthogonal :
    ∀ ε : Bool, Continuous (fun θ : ℝ => GL2LocalData.kR θ ε) ∧
      ∀ θ : ℝ, (GL2LocalData.kR θ ε).val * (GL2LocalData.kR θ ε).valᵀ = 1 := by
  intro ε
  refine ⟨?_, fun θ => ?_⟩
  · unfold GL2LocalData.kR
    exact continuous_rot.mul continuous_const
  · have hr := rot_orth θ
    cases ε
    · simpa [GL2LocalData.kR] using hr
    · have hd : ((dg2 (1 : ℝˣ) (-1) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
          ((dg2 (1 : ℝˣ) (-1) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      simp only [GL2LocalData.kR, if_true, Units.val_mul, Matrix.transpose_mul]
      calc _ = (GL2LocalData.rotR θ).val * (((dg2 (1 : ℝˣ) (-1) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
              ((dg2 (1 : ℝˣ) (-1) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) * (GL2LocalData.rotR θ).valᵀ := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hd, Matrix.mul_one, hr]

end GlobalTheory.CompanionTheory.GL2Factorization.OrthParam
