import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetOperatorBideterminantBasisReprIsAlgebraic
import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
open Formalism.L2.Ker MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JetAlg.repr_jetOp_isAlgebraic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FJetOperatorBideterminantBasisReprIsAlgebraic.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.jetOperator_bideterminantBasis_repr_isAlgebraic : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight a) (lam' : ι → Formalism.BasicNotions.DomWeight b) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ), (∀ m, IsAlgebraic ℚ (J m)) → JetInVV ℂ lam lam' nn → ∀ (i : Formalism.L2.DIV.VVIdx lam') (j : Formalism.L2.DIV.VVIdx lam), IsAlgebraic ℚ ((Formalism.L2.DIV.bVV ℂ lam').repr (jetOp lam lam' J nn (Formalism.L2.DIV.bVV ℂ lam j)) i) := by
  first | exact @GlobalTheory.JetAlg.repr_jetOp_isAlgebraic | exact GlobalTheory.JetAlg.repr_jetOp_isAlgebraic | (intros; apply GlobalTheory.JetAlg.repr_jetOp_isAlgebraic <;> assumption)
