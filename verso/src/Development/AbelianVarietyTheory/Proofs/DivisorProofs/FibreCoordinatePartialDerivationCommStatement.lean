import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCoordinatePartialDerivationComm
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AnPer.dw_comm` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFibreCoordinatePartialDerivationComm.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.fibreCoordinatePartialDerivation_comm : ∀ (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W), dw a (dw b x) = dw b (dw a x) := by
  first | exact @GlobalTheory.AnPer.dw_comm | exact GlobalTheory.AnPer.dw_comm | (intros; apply GlobalTheory.AnPer.dw_comm <;> assumption)
