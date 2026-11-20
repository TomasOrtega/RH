import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

/- English proof (translation)
Introduce `P R₁ B B₁ _ _ _ _ _ f₁ a₁ c₁ hf hc hcomp hker ha`. Use `set K := RingHom.ker f₁ with hK`. Set `σ : P ⧸ K ≃+* R₁` to `RingHom.quotientKerEquivOfSurjective hf`. Establish `hσ : ((a₁.comp (σ : P ⧸ K →+* R₁))).Flat` using `RingHom.Flat.comp (RingHom.Flat.of_bijective σ.bijective) ha`. Use `letI : Algebra (P ⧸ K) B₁ := (a₁.comp (σ : P ⧸ K →+* R₁)).toAlgebra`.

Use `haveI : Module.Flat (P ⧸ K) B₁ := hσ`. Use `letI : Algebra P B₁ := (c₁.comp (algebraMap P B)).toAlgebra`. Set `g : B →ₗ[P] B₁` to `{ toFun := c₁ map_add' := c₁.map_add map_smul' := fun p b => by`. Simplify using `only [RingHom.id_apply, Algebra.smul_def, map_mul]`. Use `rfl }`.

Establish `hg : ∀ b, g b = c₁ b` using `fun _ => rfl`. Establish `hkerg : LinearMap.ker g = (K • ⊤ : Submodule P B)`. Use extensionality with `b`. Rewrite using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hker, LinearMap.mem_ker, RingHom.mem_ker, hg]`. Establish `hle : (K • ⊤ : Submodule P B) ≤ LinearMap.ker g` using `hkerg.ge`.

Set `e₀` to `(K • ⊤ : Submodule P B).liftQ g hle`. Establish `he₀ : Function.Bijective e₀`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← LinearMap.ker_eq_bot]`. Conclude with `Submodule.ker_liftQ_eq_bot _ _ _ hkerg.le`.

Rewrite using `[← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]`. Conclude with `hc`. Set `e : (B ⧸ (K • ⊤ : Submodule P B)) ≃ₗ[P ⧸ K] B₁` to `LinearEquiv.ofBijective { toFun := e₀ map_add' := e₀.map_add map_smul' := fun q x => by`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Establish `h1 : (Ideal.Quotient.mk K p) • x = p • x`.

Rewrite using `[← IsScalarTower.algebraMap_smul (P ⧸ K) p x]`. Both sides reduce to the same expression. Rewrite using `[h1, e₀.map_smul, RingHom.id_apply]`. Express the relevant statement in the definitionally equal form `(c₁.comp (algebraMap P B)) p * e₀ x = a₁ (σ (Ideal.Quotient.mk K p)) * e₀ x`. Rewrite using `[RingHom.quotientKerEquivOfSurjective_apply_mk, hcomp]`.

Use `rfl }`. Use `he₀`. Conclude with `Module.Flat.of_linearEquiv e`.
-/
theorem flat_quot_smul_top_of_surj_flat :
    ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B]
      (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ →
      Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ →
      RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat →
      Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := by
  intro P R₁ B B₁ _ _ _ _ _ f₁ a₁ c₁ hf hc hcomp hker ha
  set K := RingHom.ker f₁ with hK
  let σ : P ⧸ K ≃+* R₁ := RingHom.quotientKerEquivOfSurjective hf
  have hσ : ((a₁.comp (σ : P ⧸ K →+* R₁))).Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective σ.bijective) ha
  letI : Algebra (P ⧸ K) B₁ := (a₁.comp (σ : P ⧸ K →+* R₁)).toAlgebra
  haveI : Module.Flat (P ⧸ K) B₁ := hσ
  letI : Algebra P B₁ := (c₁.comp (algebraMap P B)).toAlgebra
  let g : B →ₗ[P] B₁ :=
    { toFun := c₁
      map_add' := c₁.map_add
      map_smul' := fun p b => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        rfl }
  have hg : ∀ b, g b = c₁ b := fun _ => rfl
  have hkerg : LinearMap.ker g = (K • ⊤ : Submodule P B) := by
    ext b
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hker, LinearMap.mem_ker,
      RingHom.mem_ker, hg]
  have hle : (K • ⊤ : Submodule P B) ≤ LinearMap.ker g := hkerg.ge
  let e₀ := (K • ⊤ : Submodule P B).liftQ g hle
  have he₀ : Function.Bijective e₀ := by
    constructor
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ hkerg.le
    · rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
      exact hc
  let e : (B ⧸ (K • ⊤ : Submodule P B)) ≃ₗ[P ⧸ K] B₁ :=
    LinearEquiv.ofBijective
      { toFun := e₀
        map_add' := e₀.map_add
        map_smul' := fun q x => by
          obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
          have h1 : (Ideal.Quotient.mk K p) • x = p • x := by
            rw [← IsScalarTower.algebraMap_smul (P ⧸ K) p x]
            rfl
          rw [h1, e₀.map_smul, RingHom.id_apply]
          change (c₁.comp (algebraMap P B)) p * e₀ x = a₁ (σ (Ideal.Quotient.mk K p)) * e₀ x
          rw [RingHom.quotientKerEquivOfSurjective_apply_mk, hcomp]
          rfl }
      he₀
  exact Module.Flat.of_linearEquiv e

end GlobalTheory
