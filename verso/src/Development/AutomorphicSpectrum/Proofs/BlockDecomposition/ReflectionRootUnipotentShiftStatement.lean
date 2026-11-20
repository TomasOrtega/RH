import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReflectionRootUnipotentShift
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SwapRoot.Unip.sR_uR_mul_unip` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FReflectionRootUnipotentShift.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.reflection_root_unipotent_shift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (v : GU σ n), IsUnipU v →
    ∃ y : L, ∀ x : L, ∃ b : GU σ n, IsUnipU b ∧
      sR σ hσ a h * uR σ hσ a h x * v = b * (sR σ hσ a h * uR σ hσ a h (x + y)) := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.Unip.sR_uR_mul_unip | exact GlobalTheory.CompanionTheory.SwapRoot.Unip.sR_uR_mul_unip | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.Unip.sR_uR_mul_unip <;> assumption)
