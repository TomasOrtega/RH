import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFrobeniusRootSolution
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPerfectFrobeniusRootSolution.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.perfect_frobenius_root_solution : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (m n k : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Pf p B → Solv B (fun t j => a t j ^ p ^ k) (fun t => c t ^ p ^ k) → Solv B a c := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow | exact GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow <;> assumption)
