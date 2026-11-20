import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKuennethMayerVietorisRight.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.kuenneth_mayer_vietoris_right : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₂ : ObjectProperty E.C₂) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S)) → E.Kun (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_l | exact GlobalTheory.CompanionTheory.KunGlue.glue_l | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_l <;> assumption)
