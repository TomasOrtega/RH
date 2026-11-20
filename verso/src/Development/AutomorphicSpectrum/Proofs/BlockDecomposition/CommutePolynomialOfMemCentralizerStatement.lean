import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutePolynomialOfMemCentralizer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCommutePolynomialOfMemCentralizer.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.commute_polynomial_of_mem_centralizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (t : GA E n), t ∈ adCent d → ∀ e : Matrix (Fin n) (Fin n) E, IsPol (nrm d).val e → t.val * rm e = rm e * t.val := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm | exact GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm | (intros; apply GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm <;> assumption)
