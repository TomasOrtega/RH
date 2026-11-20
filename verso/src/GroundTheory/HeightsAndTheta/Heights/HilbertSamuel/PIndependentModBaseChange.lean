import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIndependentModBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial TensorProduct

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem IndependentModBaseChange.proof : IndependentModBaseChange.Statement := by
  intro σ P r g hg
  let θ : MvPolynomial σ ℂ →ₐ[ℂ] ℂ ⊗[ℤ] (MvPolynomial σ ℤ ⧸ P) :=
    (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ ℤ P)).comp
      (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ).symm.toAlgHom
  have hθ : ∀ p : MvPolynomial σ ℤ,
      θ (MvPolynomial.map (Int.castRingHom ℂ) p) = (1 : ℂ) ⊗ₜ Ideal.Quotient.mk P p := by
    intro p
    have h1 : MvPolynomial.map (Int.castRingHom ℂ) p =
        MvPolynomial.algebraTensorAlgEquiv ℤ ℂ ((1 : ℂ) ⊗ₜ p) := by
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
      congr 1
    rw [h1]
    change Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ ℤ P)
      ((MvPolynomial.algebraTensorAlgEquiv ℤ ℂ).symm (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ ((1 : ℂ) ⊗ₜ p))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have hle : ∀ a ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ)), θ a = 0 := by
    have hker : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker θ := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, hθ, Ideal.Quotient.eq_zero_iff_mem.mpr hp, tmul_zero]
    exact fun a ha => hker ha
  let ψ := Ideal.Quotient.liftₐ _ θ hle
  have key : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[ℤ] Ideal.Quotient.mk P (g i)) :=
    Module.Flat.linearIndependent_one_tmul hg
  have hfun : (ψ.toLinearMap ∘ fun i => Ideal.Quotient.mk (P.map (MvPolynomial.map (Int.castRingHom ℂ)))
      (MvPolynomial.map (Int.castRingHom ℂ) (g i))) = fun i => (1 : ℂ) ⊗ₜ[ℤ] Ideal.Quotient.mk P (g i) := by
    funext i
    exact hθ (g i)
  rw [← hfun] at key
  exact key.of_comp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
