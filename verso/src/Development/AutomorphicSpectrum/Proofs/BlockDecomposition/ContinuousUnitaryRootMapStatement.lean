import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryRootMap
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousUnitaryRootMap.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.continuous_unitary_root_map : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n), Continuous (uR σ hU.1 a h : L → GU σ n) := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.continuous_uR | exact GlobalTheory.CompanionTheory.SwapRoot.continuous_uR | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.continuous_uR <;> assumption)
