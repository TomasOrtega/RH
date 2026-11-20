import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInftyStatement
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ : ∀ (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (a : ℕ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[k] γ = f) → _root_.GlobalTheory.QFam.HasQ N f a → _root_.ReciprocityTheory.ChartRestriction.L1.IsMF k f := by
  intro N k f a hN hinv h
  refine ⟨{ toFun := f, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ },
    fun _ => rfl⟩
  · rintro _ ⟨γ, rfl⟩
    exact (ModularForm.SL_slash f γ).symm.trans (hinv γ)
  · exact h.mdifferentiable hN
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [hinv γ]
    exact (_root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN h).2

end GlobalTheory.QFam
