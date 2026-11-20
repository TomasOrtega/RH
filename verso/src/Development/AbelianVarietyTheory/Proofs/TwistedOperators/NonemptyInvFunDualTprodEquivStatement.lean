import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunDualTprodEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNonemptyInvFunDualTprodEquiv.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.nonempty_invFun_dual_tprod_equiv_intertwiningMap : ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (σ : Representation ℂ G W), Nonempty (invFun (ρ.dual.tprod σ) ≃ₗ[ℂ] σ.IntertwiningMap ρ) := by
  first | exact @GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv | exact GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv | (intros; apply GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv <;> assumption)
