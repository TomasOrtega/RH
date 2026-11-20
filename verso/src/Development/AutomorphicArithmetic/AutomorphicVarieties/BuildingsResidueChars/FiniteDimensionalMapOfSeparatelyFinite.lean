import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Introduce `M _ _ X Y S Φ V₁ V₂ h₁ h₂ hrow hcol`. Take `⟨T, hT⟩` from `exists_finset_eval_eq_zero V₁`. Establish `mem : ∀ g ∈ S.map Φ, ∀ x, (fun y => g (x, y)) ∈ V₂`. Introduce and unpack `g ⟨m, hm, rfl⟩ x`. Conclude with `hcol m hm x`.

Establish `memr : ∀ g ∈ S.map Φ, ∀ y, (fun x => g (x, y)) ∈ V₁`. Introduce and unpack `g ⟨m, hm, rfl⟩ y`. Conclude with `hrow m hm y`. Set `F : S.map Φ →ₗ[ℂ] (T → V₂)` to `LinearMap.pi fun t => LinearMap.codRestrict V₂ ((LinearMap.funLeft ℂ ℂ (fun y : Y => ((t : X), y))).comp (S.map Φ).subtype) (fun g => mem g.1 g.2 t)`. Establish `hF : Function.Injective F`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `g hg`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `p`. Take `⟨x, y⟩` from `p`.

Establish `h0` using `hT (fun x => g.1 (x, y)) (memr g.1 g.2 y) (by`. Introduce `t ht`. Use `congrArg (fun v : T → V₂ => ((v ⟨t, ht⟩ : V₂) : Y → ℂ) y) hg` as an intermediate fact. Simplify `this)` using `[F, LinearMap.funLeft]`. Simplify using `using congrFun h0 x`.

Conclude with `Module.Finite.of_injective F hF`.
-/
theorem UpperTheory.finiteDimensional_map_of_separately_finite :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X Y : Type) (S : Submodule ℂ M) (Φ : M →ₗ[ℂ] (X × Y → ℂ)) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ → (∀ m ∈ S, ∀ y, (fun x => Φ m (x, y)) ∈ V₁) → (∀ m ∈ S, ∀ x, (fun y => Φ m (x, y)) ∈ V₂) → FiniteDimensional ℂ (S.map Φ) := by
  intro M _ _ X Y S Φ V₁ V₂ h₁ h₂ hrow hcol
  obtain ⟨T, hT⟩ := exists_finset_eval_eq_zero V₁
  have mem : ∀ g ∈ S.map Φ, ∀ x, (fun y => g (x, y)) ∈ V₂ := by
    rintro g ⟨m, hm, rfl⟩ x
    exact hcol m hm x
  have memr : ∀ g ∈ S.map Φ, ∀ y, (fun x => g (x, y)) ∈ V₁ := by
    rintro g ⟨m, hm, rfl⟩ y
    exact hrow m hm y
  let F : S.map Φ →ₗ[ℂ] (T → V₂) :=
    LinearMap.pi fun t => LinearMap.codRestrict V₂
      ((LinearMap.funLeft ℂ ℂ (fun y : Y => ((t : X), y))).comp (S.map Φ).subtype)
      (fun g => mem g.1 g.2 t)
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    apply Subtype.ext
    funext p
    obtain ⟨x, y⟩ := p
    have h0 := hT (fun x => g.1 (x, y)) (memr g.1 g.2 y) (by
      intro t ht
      have := congrArg (fun v : T → V₂ => ((v ⟨t, ht⟩ : V₂) : Y → ℂ) y) hg
      simpa [F, LinearMap.funLeft] using this)
    simpa using congrFun h0 x
  exact Module.Finite.of_injective F hF
