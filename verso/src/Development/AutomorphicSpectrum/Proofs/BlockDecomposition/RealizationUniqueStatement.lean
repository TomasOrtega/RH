import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnique
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRealizationUnique.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.realization_unique : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j) (f f' : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho x f' → f = f' := by
  first | exact @GlobalTheory.CompanionTheory.KapUniq.rho_unique | exact GlobalTheory.CompanionTheory.KapUniq.rho_unique | (intros; apply GlobalTheory.CompanionTheory.KapUniq.rho_unique <;> assumption)
