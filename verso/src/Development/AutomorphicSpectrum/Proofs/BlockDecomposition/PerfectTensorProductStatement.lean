import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorProduct
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PerfectRing.pf_tensor` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPerfectTensorProduct.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.perfect_tensor_product : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K → Pf p (B ⊗[A] K) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.pf_tensor | exact GlobalTheory.CompanionTheory.PerfectRing.pf_tensor | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.pf_tensor <;> assumption)
