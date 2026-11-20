import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictCompat
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPairingRestrictCompat.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.pairing_restrict_compat : ∀ {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃) {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : CH.Cn (U₁.ι ⋙ E.F₁ a) i) (y : CH.Cn (U₂.ι ⋙ E.F₂ a') j), (resU (E.F₃ c) k₃).pullC n ((E.pr U₁ U₂ U₃ h₁ h₂ ha).μ hn x y) = (E.pr U₁' U₂' U₃' h₁' h₂' ha).μ hn ((resU (E.F₁ a) k₁).pullC i x) ((resU (E.F₂ a') k₂).pullC j y) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.pr_res | exact GlobalTheory.CompanionTheory.KunGlue.pr_res | (intros; apply GlobalTheory.CompanionTheory.KunGlue.pr_res <;> assumption)
