import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeIsotropicIffInvolutionMulZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TorusCh.iso_range_iff_sg_mul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRangeIsotropicIffInvolutionMulZero.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.range_isotropic_iff_involution_mul_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (π : Matrix (Fin n) (Fin n) E), LinearMap.range (Matrix.toLin' π) ≤ perpD (conjE E) d (LinearMap.range (Matrix.toLin' π)) ↔ sg d π * π = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.iso_range_iff_sg_mul | exact GlobalTheory.CompanionTheory.TorusCh.iso_range_iff_sg_mul | (intros; apply GlobalTheory.CompanionTheory.TorusCh.iso_range_iff_sg_mul <;> assumption)
