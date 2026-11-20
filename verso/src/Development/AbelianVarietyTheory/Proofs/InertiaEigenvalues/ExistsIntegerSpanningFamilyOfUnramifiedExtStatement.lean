import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfValNonneg
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIntegerSpanningFamilyOfUnramifiedExt.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O, algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr | exact GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr | (intros; apply GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr <;> assumption)
