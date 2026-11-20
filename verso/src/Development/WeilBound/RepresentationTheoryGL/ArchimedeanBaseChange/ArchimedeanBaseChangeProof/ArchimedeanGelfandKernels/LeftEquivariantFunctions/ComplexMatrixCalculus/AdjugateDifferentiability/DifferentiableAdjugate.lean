import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigLocal

noncomputable section

open Matrix
open scoped Kronecker

namespace PositivityTheory.RgBcC.Cxf

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq ι]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dEntry {F : E → Matrix κ μ ℂ} (h : DifferentiableAt ℝ F x) (i : κ) (j : μ) :
    DifferentiableAt ℝ (fun y => F y i j) x :=
  differentiableAt_pi.1 (differentiableAt_pi.1 h i) j

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dMat {F : E → Matrix κ μ ℂ} (h : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x) : DifferentiableAt ℝ F x :=
  differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => h i j

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dMul {F : E → Matrix κ ι ℂ} {H : E → Matrix ι μ ℂ} (hF : DifferentiableAt ℝ F x) (hH : DifferentiableAt ℝ H x) :
    DifferentiableAt ℝ (fun y => F y * H y) x := by
  refine dMat fun i j => ?_
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (dEntry hF i k).mul (dEntry hH k j)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dConjT {F : E → Matrix κ μ ℂ} (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (fun y => (F y)ᴴ) x := by
  refine dMat fun i j => ?_
  simp only [Matrix.conjTranspose_apply]
  exact (dEntry hF j i).star

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dT {F : E → Matrix κ μ ℂ} (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (fun y => (F y)ᵀ) x := dMat fun i j => dEntry hF j i

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dConst (A : Matrix κ μ ℂ) : DifferentiableAt ℝ (fun _ : E => A) x := differentiableAt_const A

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem differentiable_det : Differentiable ℝ (fun A : Matrix ι ι ℂ => A.det) := by
  intro A0
  simp only [Matrix.det_apply, Units.smul_def]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_smul ?_ _
  exact (HasFDerivAt.finsetProd fun i _ =>
    (dEntry (differentiableAt_id (x := A0)) (σ i) i).hasFDerivAt).differentiableAt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem differentiable_adjugate : Differentiable ℝ (fun A : Matrix ι ι ℂ => A.adjugate) := by
  intro A0
  refine dMat fun i j => ?_
  simp only [Matrix.adjugate_apply]
  have hu : DifferentiableAt ℝ (fun A : Matrix ι ι ℂ => A.updateRow j (Pi.single i 1)) A0 := by
    refine dMat fun k l => ?_
    by_cases hk : k = j
    · subst hk
      simp only [Matrix.updateRow_self]
      exact differentiableAt_const _
    · simp only [Matrix.updateRow_ne hk]
      exact dEntry differentiableAt_id k l
  exact (differentiable_det _).comp A0 hu

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem differentiableAt_inv (A0 : Matrix ι ι ℂ) (h : A0.det ≠ 0) : DifferentiableAt ℝ (fun A : Matrix ι ι ℂ => A⁻¹) A0 := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((differentiable_det A0).inv h).smul (differentiable_adjugate A0)

end PositivityTheory.RgBcC.Cxf
