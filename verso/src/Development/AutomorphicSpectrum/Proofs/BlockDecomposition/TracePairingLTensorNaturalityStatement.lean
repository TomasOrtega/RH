import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingLTensorNaturality
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTracePairingLTensorNaturality.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.trace_pairing_lTensor_naturality : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)) {L' : Type 1} [AddCommGroup L'] [Module W L'] (g : L' →ₗ[W] L) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L'), T c k hk f (LinearMap.lTensor A g z) = T c k hk (f ∘ₗ g.baseChange K₀) z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPsi.T_lTensor | exact GlobalTheory.CompanionTheory.FrobPsi.T_lTensor | (intros; apply GlobalTheory.CompanionTheory.FrobPsi.T_lTensor <;> assumption)
