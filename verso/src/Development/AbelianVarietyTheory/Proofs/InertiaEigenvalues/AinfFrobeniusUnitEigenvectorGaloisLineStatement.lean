import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfFrobeniusUnitEigenvectorGaloisLine
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLine.sigma_unit_eigen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAinfFrobeniusUnitEigenvectorGaloisLine.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.ainf_frobenius_unit_eigenvector_galois_line : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l) (u : ℤ_[l]ˣ), IsUnit w → Per.φA l w = Per.zA l u * w → ∀ g : GQ l, ∃ z : ℤ_[l], Per.σB g (Per.aB l w) = Per.zB l z * Per.aB l w := by
  first | exact @GlobalTheory.UnitLine.sigma_unit_eigen | exact GlobalTheory.UnitLine.sigma_unit_eigen | (intros; apply GlobalTheory.UnitLine.sigma_unit_eigen <;> assumption)
