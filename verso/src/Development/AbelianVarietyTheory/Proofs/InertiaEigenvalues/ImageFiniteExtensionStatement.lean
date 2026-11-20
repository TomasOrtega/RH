import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageFiniteExtension
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_finiteDimensional_intermediateField_eq_range_fractionRing` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FImageFiniteExtension.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.image_finite_extension : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* PadicAlgCl l), (∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) → ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ ∀ y, y ∈ L ↔ ∃ a, ι a = y := by
  first | exact @GlobalTheory.exists_finiteDimensional_intermediateField_eq_range_fractionRing | exact GlobalTheory.exists_finiteDimensional_intermediateField_eq_range_fractionRing | (intros; apply GlobalTheory.exists_finiteDimensional_intermediateField_eq_range_fractionRing <;> assumption)
