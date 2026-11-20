import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIndependentModBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial TensorProduct

noncomputable section

/- English proof (translation)
Introduce `σ P r g hg`. Set `θ : MvPolynomial σ ℂ →ₐ[ℂ] ℂ ⊗[ℤ] (MvPolynomial σ ℤ ⧸ P)` to `(Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ ℤ P)).comp (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ).symm.toAlgHom`. Establish `hθ : ∀ p : MvPolynomial σ ℤ, θ (MvPolynomial.map (Int.castRingHom ℂ) p) = (1 : ℂ) ⊗ₜ Ideal.Quotient.mk P p`. Introduce `p`. Establish `h1 : MvPolynomial.map (Int.castRingHom ℂ) p = MvPolynomial.algebraTensorAlgEquiv ℤ ℂ ((1 : ℂ) ⊗ₜ p)`.

Rewrite using `[MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]`. Use `congr 1`. Rewrite using `[h1]`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ ℤ P) ((MvPolynomial.algebraTensorAlgEquiv ℤ ℂ).symm (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ ((1 : ℂ) ⊗ₜ p))) = _`. Rewrite using `[AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]`.

Both sides reduce to the same expression. Establish `hle : ∀ a ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ)), θ a = 0`. Establish `hker : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker θ`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `p hp`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hθ, Ideal.Quotient.eq_zero_iff_mem.mpr hp, tmul_zero]`. Conclude with `fun a ha => hker ha`. Set `ψ` to `Ideal.Quotient.liftₐ _ θ hle`. Establish `key : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[ℤ] Ideal.Quotient.mk P (g i))` using `Module.Flat.linearIndependent_one_tmul hg`. Establish `hfun : (ψ.toLinearMap ∘ fun i => Ideal.Quotient.mk (P.map (MvPolynomial.map (Int.castRingHom ℂ))) (MvPolynomial.map (Int.castRingHom ℂ) (g i))) = fun i => (1 : ℂ) ⊗ₜ[ℤ] Ideal.Quotient.mk P (g i)`.

Use function extensionality and compare the values at `i`. Conclude with `hθ (g i)`. Rewrite `key` using `[← hfun]`. Conclude with `key.of_comp`.
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
