import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetRealSandwich
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

namespace GlobalTheory.MatMulDet

/- English proof (translation)
Use `first`. Consider the case `(run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll]))`. Conclude with `@_root_.GlobalTheory.DeterminantRealSandwich.det_real_family`. Consider the case `(run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll]))`. Conclude with `_root_.GlobalTheory.DeterminantRealSandwich.det_real_family`.

Consider the case `exact @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family`. Consider the case `exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family`. Consider the case `(apply _root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> first | assumption | infer_instance)`.

Consider the case `(intros; exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family ..)`.
-/
theorem det_real_mul_mul (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ)
    (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] (ι → Fin j → Fin j → ℂ))
    (hL : ∀ h w, Matrix.of (L h w) = A w * Matrix.of (h w) * B w) :
    LinearMap.det L = ∏ w, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | exact @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | (apply _root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family ..)

end GlobalTheory.MatMulDet
