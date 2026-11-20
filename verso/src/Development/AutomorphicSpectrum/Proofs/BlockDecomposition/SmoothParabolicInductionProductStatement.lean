import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothParabolicInductionProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSmoothParabolicInductionProduct.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.smooth_parabolic_induction_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t N : ℕ} (h : r + t = N) (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), IsSmooth π₁ → IsSmooth π₂ → IsSmooth (sQ h π₁ π₂) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ | exact GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ | (intros; apply GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ <;> assumption)
