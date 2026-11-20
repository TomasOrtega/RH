import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeMulIdempotentRange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TorusCh.DegLam.deg_lam` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDegreeMulIdempotentRange.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.degree_mul_idempotent_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), DegAdelic → ∀ (e : Matrix (Fin n) (Fin n) E), e * e = e → ∀ t x : GA E n, t.val * rm e = rm e * t.val → deg (t * x) (LinearMap.range (Matrix.toLin' e)) = deg x (LinearMap.range (Matrix.toLin' e)) + lam e t := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.DegLam.deg_lam | exact GlobalTheory.CompanionTheory.TorusCh.DegLam.deg_lam | (intros; apply GlobalTheory.CompanionTheory.TorusCh.DegLam.deg_lam <;> assumption)
