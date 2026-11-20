import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingGaloisEquivariant
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FrobPairing.T_gal` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTracePairingGaloisEquivariant.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.trace_pairing_galois_equivariant : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (σA : A →+* A) (σC : C₀ →+* C₀) (gT : A ⊗[W] L →+ A ⊗[W] L), (∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y) → (∀ a, σC (c a) = c (σA a)) → (∀ x, σC (k x) = k x) → ∀ (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk f (gT z) = σC (T c k hk f z) := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_gal | exact GlobalTheory.CompanionTheory.FrobPairing.T_gal | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_gal <;> assumption)
