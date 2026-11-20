import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleMatrixSetTransposeImage
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ClassFin.ss_transpose | exact GlobalTheory.ClassFin.ss_transpose | (intros; apply GlobalTheory.ClassFin.ss_transpose <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.isCompletelyReducibleMatrixSet_transpose_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), SS Γ → SS (Matrix.transpose '' Γ) := by
  first | exact @GlobalTheory.ClassFin.ss_transpose | exact GlobalTheory.ClassFin.ss_transpose | (intros; apply GlobalTheory.ClassFin.ss_transpose <;> assumption)
