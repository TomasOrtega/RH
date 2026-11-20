import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntBilinFormDescendAlongSurjectiveStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace OrbMark

/- English proof (translation)
Introduce `O _ bar w0 X₀ _ _ v hv hp X _ _ _ β hβ k β' hk`. Take `⟨τ, f, -, hf, -, H⟩` from `GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator w0 v β hβ`. Establish `hval : ∀ (x₀ y₀ : X₀), ∃ x y, v x₀ y₀ = β x y`. Introduce `x₀ y₀`. Take `⟨x, hx⟩` from `hf (Submodule.Quotient.mk x₀)`.

Take `⟨y, hy⟩` from `hf (Submodule.Quotient.mk y₀)`. Conclude with `⟨x, y, (H x y x₀ y₀ hx.symm hy.symm).symm⟩`. Establish `hβ' : ∀ x y, (k : ℤ) * β' x y = β x y` using `fun x y => by rw [← hk]; simp`. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. It suffices to derive a contradiction.

Establish `hv0 : v = 0` using `LinearMap.ext₂ fun x₀ y₀ => by`. Take `⟨x, y, e⟩` from `hval x₀ y₀`. Rewrite using `[e, ← hβ']`. Simplify using the standard rewrite rules. Conclude with `zero_ne_one (hp 0 0 (Subtype.ext (by simp [hv0])))`.

Establish `hkz : (k : ℤ) ≠ 0` using `by exact_mod_cast hk0.ne'`. Establish `hcan : ∀ {a b : ℤ}, (k : ℤ) * a = k * b → a = b` using `fun h => mul_left_cancel₀ hkz h`. Establish `hl : ∀ x, f x = 0 → ∀ y, β' x y = 0`. Introduce `x hx y`. Take `⟨y₀, hy₀⟩` from `Submodule.Quotient.mk_surjective _ (f y)`.

Establish `e` using `H x y 0 y₀ (by rw [hx]; rfl) hy₀`. Apply `hcan` to reduce the goal to its premises. Rewrite using `[hβ', e]`. Simplify using the standard rewrite rules. Establish `hr : ∀ x, f x = 0 → ∀ y, β' y x = 0`.

Introduce `x hx y`. Take `⟨y₀, hy₀⟩` from `Submodule.Quotient.mk_surjective _ (f y)`. Establish `e` using `H y x y₀ 0 hy₀ (by rw [hx]; rfl)`. Apply `hcan` to reduce the goal to its premises. Rewrite using `[hβ', e]`.

Simplify using the standard rewrite rules. Take `⟨ζ₁, hζ₁⟩` from `GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf β' hl hr`. Set `m : X₀ →ₗ[ℤ] X₀ ⧸ (CarDim.orad v : Submodule O X₀)` to `(CarDim.orad v : Submodule O X₀).mkQ.toAddMonoidHom.toIntLinearMap`. Set `ζ : LinearMap.BilinForm ℤ X₀` to `ζ₁.compl₁₂ m m`. Establish `hζ : ∀ x₀ y₀, (k : ℤ) * ζ x₀ y₀ = v x₀ y₀`.

Introduce `x₀ y₀`. Take `⟨x, hx⟩` from `hf (Submodule.Quotient.mk x₀)`. Take `⟨y, hy⟩` from `hf (Submodule.Quotient.mk y₀)`. Establish `e1 : ζ x₀ y₀ = β' x y` using `by show ζ₁ (Submodule.Quotient.mk x₀) (Submodule.Quotient.mk y₀) = _`. Rewrite using `[← hx, ← hy, hζ₁]`.

Rewrite using `[e1, hβ', H x y x₀ y₀ hx.symm hy.symm]`. Establish `hmem : ζ ∈ balForms bar X₀`. Use `⟨fun y z => hcan ?_, fun a y z => hcan ?_⟩` and prove the remaining obligations. Rewrite using `[hζ, hζ, hv.1]`. Rewrite using `[hζ, hζ, hv.2]`.

Use `hp k ⟨ζ, hmem⟩ (Subtype.ext (LinearMap.ext₂ fun x₀ y₀ => ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `v x₀ y₀ = ((k • ζ : LinearMap.BilinForm ℤ X₀)) x₀ y₀`. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, nsmul_eq_mul, hζ]`.
-/
theorem eq_one_of_smul_eq_of_orbFun_evalZ_eq_one :
    ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀]
      (v : LinearMap.BilinForm ℤ X₀) (hv : v ∈ balForms bar X₀), IsPrim bar (⟨v, hv⟩ : balForms bar X₀) →
      ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X),
        (OrbMark.orbFun O w0 v).evalZ β = 1 →
        ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  intro O _ bar w0 X₀ _ _ v hv hp X _ _ _ β hβ k β' hk
  obtain ⟨τ, f, -, hf, -, H⟩ := GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator w0 v β hβ
  have hval : ∀ (x₀ y₀ : X₀), ∃ x y, v x₀ y₀ = β x y := by
    intro x₀ y₀
    obtain ⟨x, hx⟩ := hf (Submodule.Quotient.mk x₀)
    obtain ⟨y, hy⟩ := hf (Submodule.Quotient.mk y₀)
    exact ⟨x, y, (H x y x₀ y₀ hx.symm hy.symm).symm⟩
  have hβ' : ∀ x y, (k : ℤ) * β' x y = β x y := fun x y => by rw [← hk]; simp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exfalso
    have hv0 : v = 0 := LinearMap.ext₂ fun x₀ y₀ => by
      obtain ⟨x, y, e⟩ := hval x₀ y₀
      rw [e, ← hβ']
      simp
    exact zero_ne_one (hp 0 0 (Subtype.ext (by simp [hv0])))
  · have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hcan : ∀ {a b : ℤ}, (k : ℤ) * a = k * b → a = b := fun h => mul_left_cancel₀ hkz h
    have hl : ∀ x, f x = 0 → ∀ y, β' x y = 0 := by
      intro x hx y
      obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ (f y)
      have e := H x y 0 y₀ (by rw [hx]; rfl) hy₀
      apply hcan
      rw [hβ', e]
      simp
    have hr : ∀ x, f x = 0 → ∀ y, β' y x = 0 := by
      intro x hx y
      obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ (f y)
      have e := H y x y₀ 0 hy₀ (by rw [hx]; rfl)
      apply hcan
      rw [hβ', e]
      simp
    obtain ⟨ζ₁, hζ₁⟩ := GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf β' hl hr
    let m : X₀ →ₗ[ℤ] X₀ ⧸ (CarDim.orad v : Submodule O X₀) :=
      (CarDim.orad v : Submodule O X₀).mkQ.toAddMonoidHom.toIntLinearMap
    let ζ : LinearMap.BilinForm ℤ X₀ := ζ₁.compl₁₂ m m
    have hζ : ∀ x₀ y₀, (k : ℤ) * ζ x₀ y₀ = v x₀ y₀ := by
      intro x₀ y₀
      obtain ⟨x, hx⟩ := hf (Submodule.Quotient.mk x₀)
      obtain ⟨y, hy⟩ := hf (Submodule.Quotient.mk y₀)
      have e1 : ζ x₀ y₀ = β' x y := by
        show ζ₁ (Submodule.Quotient.mk x₀) (Submodule.Quotient.mk y₀) = _
        rw [← hx, ← hy, hζ₁]
      rw [e1, hβ', H x y x₀ y₀ hx.symm hy.symm]
    have hmem : ζ ∈ balForms bar X₀ := by
      refine ⟨fun y z => hcan ?_, fun a y z => hcan ?_⟩
      · rw [hζ, hζ, hv.1]
      · rw [hζ, hζ, hv.2]
    refine hp k ⟨ζ, hmem⟩ (Subtype.ext (LinearMap.ext₂ fun x₀ y₀ => ?_))
    change v x₀ y₀ = ((k • ζ : LinearMap.BilinForm ℤ X₀)) x₀ y₀
    rw [LinearMap.smul_apply, LinearMap.smul_apply, nsmul_eq_mul, hζ]

end OrbMark

end GlobalTheory.PolFan
