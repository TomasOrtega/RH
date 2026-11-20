import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentX
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMvPowerSeriesAlgHomExtOfIsNilpotentX.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], ∀ φ ψ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) → (∀ i, φ (X i) = ψ (X i)) → φ = ψ := by
  first | exact @GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent | exact GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent | (intros; apply GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent <;> assumption)
