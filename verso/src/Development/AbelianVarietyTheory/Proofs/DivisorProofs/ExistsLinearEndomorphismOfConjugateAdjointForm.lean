import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

namespace GlobalTheory.GramAdj

/- English proof (translation)
Introduce `E _ _ _ H D β hl hr hs`. Set `f : D.La → (D.La →ₗ[ℤ] ℤ)` to `fun x => (AddMonoidHom.mk' (β x) (hr x)).toIntLinearMap`. Establish `hf : ∀ x y, f x y = β x y` using `fun _ _ => rfl`. Set `e` to `Equiv.ofBijective D.EF D.unimod`. Establish `he : ∀ g, D.EF (e.symm g) = g` using `fun g => e.apply_symm_apply g`.

Establish `key : ∀ x y, D.EF (e.symm (f x)) y = β x y` using `fun x y => by rw [he, hf]`. Establish `hadd : ∀ x x', e.symm (f (x + x')) = e.symm (f x) + e.symm (f x')`. Introduce `x x'`. Apply `D.unimod.1` to reduce the goal to its premises. Use extensionality with `y`.

Simplify using `only [map_add, LinearMap.add_apply, key, hl]`. Use `⟨AddMonoidHom.mk' (fun x => e.symm (f x)) hadd, ?_, ?_⟩` and prove the remaining obligations. Introduce `s x show e.symm (f (s • x)) = s • e.symm (f x)`. Apply `D.unimod.1` to reduce the goal to its premises. Use extensionality with `y`.

Rewrite using `[key, hs, ← key, D.adj]`. Introduce `x y show β x y = D.EF (e.symm (f x)) y`. Rewrite using `[key]`.
-/
theorem exists_endo_of_adjoint :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (β : D.La → D.La → ℤ), (∀ x y z, β (x + y) z = β x z + β y z) → (∀ x y z, β x (y + z) = β x y + β x z) → (∀ (s : 𝓞 E) x y, β (s • x) y = β x (H.bar s • y)) → ∃ γ : D.La →+ D.La, (∀ (s : 𝓞 E) x, γ (s • x) = s • γ x) ∧ ∀ x y, β x y = D.EF (γ x) y := by
  intro E _ _ _ H D β hl hr hs
  let f : D.La → (D.La →ₗ[ℤ] ℤ) := fun x => (AddMonoidHom.mk' (β x) (hr x)).toIntLinearMap
  have hf : ∀ x y, f x y = β x y := fun _ _ => rfl
  let e := Equiv.ofBijective D.EF D.unimod
  have he : ∀ g, D.EF (e.symm g) = g := fun g => e.apply_symm_apply g
  have key : ∀ x y, D.EF (e.symm (f x)) y = β x y := fun x y => by rw [he, hf]
  have hadd : ∀ x x', e.symm (f (x + x')) = e.symm (f x) + e.symm (f x') := by
    intro x x'
    apply D.unimod.1
    ext y
    simp only [map_add, LinearMap.add_apply, key, hl]
  refine ⟨AddMonoidHom.mk' (fun x => e.symm (f x)) hadd, ?_, ?_⟩
  · intro s x
    show e.symm (f (s • x)) = s • e.symm (f x)
    apply D.unimod.1
    ext y
    rw [key, hs, ← key, D.adj]
  · intro x y
    show β x y = D.EF (e.symm (f x)) y
    rw [key]

end GlobalTheory.GramAdj
