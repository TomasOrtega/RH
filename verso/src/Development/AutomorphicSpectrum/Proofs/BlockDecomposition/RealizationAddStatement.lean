import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAdd
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRealizationAdd.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.realization_add : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ} (x y : ∀ n, C.S n j) (f g : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho y g → C.Rho (x + y) (f + g) := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.rho_add | exact GlobalTheory.CompanionTheory.KapRho.rho_add | (intros; apply GlobalTheory.CompanionTheory.KapRho.rho_add <;> assumption)
