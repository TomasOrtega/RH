import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem relLen_chain_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ),
    RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  intro C _ v M _ _ X'' X' X r₁ r₂ h₂ h₁
  obtain ⟨n, b, b', A, hA, hr₂⟩ := h₂
  obtain ⟨m, c, c', B, hB, hr₁⟩ := h₁
  have hnm : n = m := by simpa using Fintype.card_congr (b.indexEquiv c')
  subst hnm
  have hU : ∀ i, (b i : M) = ∑ j, c'.toMatrix b j i • (c' j : M) := by
    intro i
    have := congrArg X'.subtype (c'.sum_repr (b i))
    simp only [map_sum, map_smul, Submodule.subtype_apply] at this
    simp only [Basis.toMatrix_apply]
    exact this.symm
  have u : IsUnit (c'.toMatrix b).det := by
    let _ := c'.invertibleToMatrix b
    exact Matrix.isUnit_det_of_invertible _
  refine ⟨n, c, b', B * c'.toMatrix b * A, fun k => ?_, ?_⟩
  · rw [hA k]
    simp_rw [hU, hB, Finset.smul_sum, smul_smul]
    simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_smul]
    refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    congr 1
    ring
  · rw [Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul, v.map_mul,
      v_unit v u, add_zero, hr₁, hr₂]
    rfl

end GlobalTheory
