import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KchainSt

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbBase

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def entL (a b : Fin n) : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)

/- English proof (translation)
The claim follows from `(entL a b).contDiff`.
-/
theorem contDiff_entry (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) := (entL a b).contDiff

/- English proof (translation)
The claim follows from `contDiffAt_pi' fun a => contDiffAt_pi' fun b => h a b`.
-/
theorem contDiffAt_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → Mat n} {x : E}
    (h : ∀ a b, ContDiffAt ℝ ∞ (fun z => F z a b) x) : ContDiffAt ℝ ∞ F x :=
  contDiffAt_pi' fun a => contDiffAt_pi' fun b => h a b

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Conclude with `ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)`.
-/
theorem contDiff_det_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → Mat n)
    (h : ∀ a b, ContDiff ℝ ∞ (fun z => F z a b)) : ContDiff ℝ ∞ (fun z => (F z).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

/- English proof (translation)
The claim follows from `contDiff_det_of id fun a b => contDiff_entry a b`.
-/
theorem contDiff_det : ContDiff ℝ ∞ (fun y : Mat n => y.det) := contDiff_det_of id fun a b => contDiff_entry a b

/- English proof (translation)
Use `contDiffAt_of_entries fun a b => ?_` and prove the remaining obligations. Establish `e : (fun y : Mat n => y⁻¹ a b) = fun y => (y.det)⁻¹ * (y.updateRow b (Pi.single a 1)).det`. Use function extensionality and compare the values at `y`. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]`. Rewrite using `[e]`.

Use `(contDiff_det.contDiffAt.inv hx).mul (contDiff_det_of _ fun i j => ?_).contDiffAt` and prove the remaining obligations. Simplify using `only [Matrix.updateRow_apply]`. Use `split_ifs`. Conclude with `contDiff_const`. Apply the tactic sequence `exact contDiff_entry _ _`.
-/
theorem contDiffAt_inv {x : Mat n} (hx : x.det ≠ 0) : ContDiffAt ℝ ∞ (fun y : Mat n => y⁻¹) x := by
  refine contDiffAt_of_entries fun a b => ?_
  have e : (fun y : Mat n => y⁻¹ a b) = fun y => (y.det)⁻¹ * (y.updateRow b (Pi.single a 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  rw [e]
  refine (contDiff_det.contDiffAt.inv hx).mul (contDiff_det_of _ fun i j => ?_).contDiffAt
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry _ _

end PositivityTheory.RgBcC.LfSt.Kchain.KbBase
