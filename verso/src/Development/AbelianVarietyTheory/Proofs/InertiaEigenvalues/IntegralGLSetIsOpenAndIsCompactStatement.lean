import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLSetIsOpenAndIsCompact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.JR.GLift.glO_isOpen_isCompact | exact GlobalTheory.JR.GLift.glO_isOpen_isCompact | (intros; apply GlobalTheory.JR.GLift.glO_isOpen_isCompact <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.integralGLSet_isOpen_and_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by
  first | exact @GlobalTheory.JR.GLift.glO_isOpen_isCompact | exact GlobalTheory.JR.GLift.glO_isOpen_isCompact | (intros; apply GlobalTheory.JR.GLift.glO_isOpen_isCompact <;> assumption)
