import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinGlRelationsAdjoint
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSpinGlRelationsAdjoint.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.spin_gl_relations_adjoint : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    Formalism.REAL.GlRel (spinM c) ∧ ∀ a b, (spinM c a b)ᴴ = spinM c b a := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel | exact GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel | (intros; apply GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel <;> assumption)
