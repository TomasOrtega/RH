import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PeterssonNormOfUpLift

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Formalism.IndefR.Eqv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem rightInv_holds : RightInv := by
  intro H _ _ _ Γ _ ν _ _ 𝓕 h𝓕 ψ hψ k
  have hψ' : ∀ (g : Γ) (x : H), ψ (g • x) = ψ x := fun g x => hψ g g.2 x
  have h2 : IsFundamentalDomain Γ (MulOpposite.op k • 𝓕) ν := h𝓕.smul_of_comm (MulOpposite.op k)
  have himg : MulOpposite.op k • 𝓕 = (fun h => h * k) '' 𝓕 := by
    ext x
    simp [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x * k⁻¹, hx, by simp⟩
  have hmp := measurePreserving_mul_right ν k
  have hme := measurableEmbedding_mulRight (G := H) k
  constructor
  · have e1 := (hmp.integrableOn_image hme (f := ψ) (s := 𝓕)).symm
    rw [← himg] at e1
    exact e1.trans (h2.integrableOn_iff h𝓕 hψ')
  · calc ∫ h in 𝓕, ψ (h * k) ∂ν = ∫ y in (fun h => h * k) '' 𝓕, ψ y ∂ν :=
          (hmp.setIntegral_image_emb hme ψ 𝓕).symm
      _ = ∫ y in MulOpposite.op k • 𝓕, ψ y ∂ν := by rw [himg]
      _ = ∫ h in 𝓕, ψ h ∂ν := h2.setIntegral_eq h𝓕 hψ'

section GA

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem rightInvGA_holds (V : HSp D) : RightInvGA V := by
  intro hM hC hU K μ 𝓕 h ψ hψ k
  have := hM
  have := hC
  have hH : μ.IsHaarMeasure := h.1.1
  have := hU μ hH
  exact rightInv_holds (GA D V) (GQ V) μ 𝓕 h.2 ψ hψ k

end GA

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Use symmetry to reverse the relation.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem ioExistsOf_holds : IoExistsOf := by
  intro G H S Sinf Ds Dt _ _ _ _ _ _ _ ν 𝓕 th pt T CCs CCt hint hglob huniq
  choose U hU using hglob
  have key : ∀ (F : CCs) (u : CCt), (∀ φ v g, (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) g =
      Lift.liftInt ν 𝓕 th (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) g) → u = U F := by
    intro F u hu
    refine sub_eq_zero.1 (huniq _ fun φ v => ?_)
    funext g
    simp [hu, hU]
  refine ⟨{ toFun := U, map_add' := ?_, map_smul' := ?_ }, ⟨hint, fun F φ v g => (hU F φ v g).symm⟩⟩
  · intro F1 F2
    symm
    apply key
    intro φ v g
    simp only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply, hU]
    unfold Lift.liftInt
    rw [← integral_add (hint F1 φ v g) (hint F2 φ v g)]
    congr 1
    funext h
    simp only [Pi.add_apply]
    ring
  · intro c F
    symm
    apply key
    intro φ v g
    simp only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hU, RingHom.id_apply]
    unfold Lift.liftInt
    rw [← integral_const_mul]
    congr 1
    funext h
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end Formalism.IndefR.Eqv

end
