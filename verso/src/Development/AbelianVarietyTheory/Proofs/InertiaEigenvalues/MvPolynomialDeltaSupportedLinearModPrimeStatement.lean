import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MvPolynomialDeltaSupportedLinearModPrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.polyDelta_supported_linear_mod` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMvPolynomialDeltaSupportedLinearModPrime.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.mvPolynomialDelta_supported_linear_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (i : ℕ), ∀ s ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic (i + 1)) ∧ ∃ a ∈ MvPolynomial.supported A (Set.Iic i), ∃ b ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s - (a * MvPolynomial.X (i + 1) + b) ∈ Ideal.span {(l : MvPolynomial ℕ A)} := by
  first | exact @GlobalTheory.BSP.polyDelta_supported_linear_mod | exact GlobalTheory.BSP.polyDelta_supported_linear_mod | (intros; apply GlobalTheory.BSP.polyDelta_supported_linear_mod <;> assumption)
