import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PeterssonNormOfUpLift

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Formalism.IndefR.Eqv

/- English proof (translation)
Introduce `H _ _ _ Γ _ ν _ _ 𝓕 h𝓕 ψ hψ k`. Establish `hψ' : ∀ (g : Γ) (x : H), ψ (g • x) = ψ x` using `fun g x => hψ g g.2 x`. Establish `h2 : IsFundamentalDomain Γ (MulOpposite.op k • 𝓕) ν` using `h𝓕.smul_of_comm (MulOpposite.op k)`. Establish `himg : MulOpposite.op k • 𝓕 = (fun h => h * k) '' 𝓕`. Use extensionality with `x`.

Simplify using `[Set.mem_smul_set]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`. Introduce `hx`.

Conclude with `⟨x * k⁻¹, hx, by simp⟩`. Establish `hmp` using `measurePreserving_mul_right ν k`. Establish `hme` using `measurableEmbedding_mulRight (G := H) k`. Prove the components needed by the constructor for the conclusion. Establish `e1` using `(hmp.integrableOn_image hme (f := ψ) (s := 𝓕)).symm`.

Rewrite `e1` using `[← himg]`. Conclude with `e1.trans (h2.integrableOn_iff h𝓕 hψ')`. Combine the equalities or inequalities in the displayed calculation.
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
Introduce `hM hC hU K μ 𝓕 h ψ hψ k`. Use `hM` as an intermediate fact. Use `hC` as an intermediate fact. Establish `hH : μ.IsHaarMeasure` using `h.1.1`. Use `hU μ hH` as an intermediate fact.

Conclude with `rightInv_holds (GA D V) (GQ V) μ 𝓕 h.2 ψ hψ k`.
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
Introduce `G H S Sinf Ds Dt _ _ _ _ _ _ _ ν 𝓕 th pt T CCs CCt hint hglob huniq`. Use `choose U hU using hglob`. Establish `key : ∀ (F : CCs) (u : CCt), (∀ φ v g, (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) g = Lift.liftInt ν 𝓕 th (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) g) → u = U F`. Introduce `F u hu`. Use `sub_eq_zero.1 (huniq _ fun φ v => ?_)` and prove the remaining obligations.

Use function extensionality and compare the values at `g`. Simplify using `[hu, hU]`. Use `⟨{ toFun := U, map_add' := ?_, map_smul' := ?_ }, ⟨hint, fun F φ v g => (hU F φ v g).symm⟩⟩` and prove the remaining obligations. Introduce `F1 F2`. Use `symm`.

Apply `key` to reduce the goal to its premises. Introduce `φ v g`. Simplify using `only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply, hU]`. Unfold `Lift.liftInt`. Rewrite using `[← integral_add (hint F1 φ v g) (hint F2 φ v g)]`.

Use `congr 1`. Use function extensionality and compare the values at `h`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c F`.

Use `symm`. Apply `key` to reduce the goal to its premises. Introduce `φ v g`. Simplify using `only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hU, RingHom.id_apply]`. Unfold `Lift.liftInt`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `h`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
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
