import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvolutionAdjoinNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsInvolutionAdjoinNorm.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.exists_involution_adjoin_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E), ∃ σ : Algebra.adjoin E {(nrm d).val} →+* Algebra.adjoin E {(nrm d).val}, (∀ x, ((σ x : Algebra.adjoin E {(nrm d).val}) : Matrix (Fin n) (Fin n) E) = sg d x) ∧ ∀ x, σ (σ x) = x := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing | exact GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing | (intros; apply GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing <;> assumption)
