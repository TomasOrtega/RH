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
The claim follows from `differentiableAt_pi.1 (differentiableAt_pi.1 h i) j`.
-/
theorem dEntry {F : E → Matrix κ μ ℂ} (h : DifferentiableAt ℝ F x) (i : κ) (j : μ) :
    DifferentiableAt ℝ (fun y => F y i j) x :=
  differentiableAt_pi.1 (differentiableAt_pi.1 h i) j

/- English proof (translation)
The claim follows from `differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => h i j`.
-/
theorem dMat {F : E → Matrix κ μ ℂ} (h : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x) : DifferentiableAt ℝ F x :=
  differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => h i j

/- English proof (translation)
Use `dMat fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply]`. Apply the tactic sequence `exact DifferentiableAt.fun_sum fun k _ => (dEntry hF i k).mul (dEntry hH k j)`.
-/
theorem dMul {F : E → Matrix κ ι ℂ} {H : E → Matrix ι μ ℂ} (hF : DifferentiableAt ℝ F x) (hH : DifferentiableAt ℝ H x) :
    DifferentiableAt ℝ (fun y => F y * H y) x := by
  refine dMat fun i j => ?_
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (dEntry hF i k).mul (dEntry hH k j)

/- English proof (translation)
Use `dMat fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.conjTranspose_apply]`. Apply the tactic sequence `exact (dEntry hF j i).star`.
-/
theorem dConjT {F : E → Matrix κ μ ℂ} (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (fun y => (F y)ᴴ) x := by
  refine dMat fun i j => ?_
  simp only [Matrix.conjTranspose_apply]
  exact (dEntry hF j i).star

/- English proof (translation)
The claim follows from `dMat fun i j => dEntry hF j i`.
-/
theorem dT {F : E → Matrix κ μ ℂ} (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (fun y => (F y)ᵀ) x := dMat fun i j => dEntry hF j i

/- English proof (translation)
The claim follows from `differentiableAt_const A`.
-/
theorem dConst (A : Matrix κ μ ℂ) : DifferentiableAt ℝ (fun _ : E => A) x := differentiableAt_const A

/- English proof (translation)
Introduce `A0`. Simplify using `only [Matrix.det_apply, Units.smul_def]`. Use `DifferentiableAt.fun_sum fun σ _ => ?_` and prove the remaining obligations. Use `DifferentiableAt.const_smul ?_ _` and prove the remaining obligations. Apply the tactic sequence `exact (HasFDerivAt.finsetProd fun i _ => (dEntry (differentiableAt_id (x := A0)) (σ i) i).hasFDerivAt).differentiableAt`.
-/
theorem differentiable_det : Differentiable ℝ (fun A : Matrix ι ι ℂ => A.det) := by
  intro A0
  simp only [Matrix.det_apply, Units.smul_def]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_smul ?_ _
  exact (HasFDerivAt.finsetProd fun i _ =>
    (dEntry (differentiableAt_id (x := A0)) (σ i) i).hasFDerivAt).differentiableAt

/- English proof (translation)
Introduce `A0`. Use `dMat fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.adjugate_apply]`. Establish `hu : DifferentiableAt ℝ (fun A : Matrix ι ι ℂ => A.updateRow j (Pi.single i 1)) A0`. Use `dMat fun k l => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `only [Matrix.updateRow_self]`. Conclude with `differentiableAt_const _`. Simplify using `only [Matrix.updateRow_ne hk]`.

Apply the tactic sequence `exact dEntry differentiableAt_id k l`. Conclude with `(differentiable_det _).comp A0 hu`.
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
Simplify using `only [Matrix.inv_def, Ring.inverse_eq_inv']`. Conclude with `((differentiable_det A0).inv h).smul (differentiable_adjugate A0)`.
-/
theorem differentiableAt_inv (A0 : Matrix ι ι ℂ) (h : A0.det ≠ 0) : DifferentiableAt ℝ (fun A : Matrix ι ι ℂ => A⁻¹) A0 := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((differentiable_det A0).inv h).smul (differentiable_adjugate A0)

end PositivityTheory.RgBcC.Cxf
