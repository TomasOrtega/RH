import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianLinearEquivContinuous
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.et_equiv_continuous` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteEtaleHermitianLinearEquivContinuous.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finiteEtaleHermitian_linearEquiv_continuous : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), Continuous j ∧ Continuous j.symm := by
  first | exact @GlobalTheory.JR.et_equiv_continuous | exact GlobalTheory.JR.et_equiv_continuous | (intros; apply GlobalTheory.JR.et_equiv_continuous <;> assumption)
