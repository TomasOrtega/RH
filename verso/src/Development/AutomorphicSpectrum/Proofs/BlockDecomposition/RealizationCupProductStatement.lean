import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationCupProduct
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRealizationCupProduct.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.realization_cup_product : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ {i j : ℕ} (x : ∀ n, C.S n i) (y : ∀ n, C.S n j) (f : Module.Dual K (C.V i) →+ B) (g : Module.Dual K (C.V j) →+ B) (h : Module.Dual K (C.V (i + j)) →+ B), C.Rho x f → C.Rho y g → C.Rho (fun n => P.cS n i j (x n) (y n)) h → ∀ {m m' : ℕ} (bs : Module.Basis (Fin m) K (C.V i)) (bs' : Module.Basis (Fin m') K (C.V j)) (φ : Module.Dual K (C.V (i + j))), h φ = ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') * C.o (φ (P.cV i j (bs s) (bs' s'))) := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.rho_cup | exact GlobalTheory.CompanionTheory.KapRho.rho_cup | (intros; apply GlobalTheory.CompanionTheory.KapRho.rho_cup <;> assumption)
