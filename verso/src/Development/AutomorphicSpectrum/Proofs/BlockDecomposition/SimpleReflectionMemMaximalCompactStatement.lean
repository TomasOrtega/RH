import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleReflectionMemMaximalCompact
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SwapRoot.sR_mem_KU | exact GlobalTheory.CompanionTheory.SwapRoot.sR_mem_KU | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.sR_mem_KU <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.simple_reflection_mem_maximal_compact : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n), sR σ hU.1 a h ∈ KU σ n := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.sR_mem_KU | exact GlobalTheory.CompanionTheory.SwapRoot.sR_mem_KU | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.sR_mem_KU <;> assumption)
