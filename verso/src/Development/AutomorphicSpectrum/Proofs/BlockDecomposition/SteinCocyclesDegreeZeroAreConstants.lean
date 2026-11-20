import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

/- English proof (translation)
Introduce `hD R _ C _ F hS`. Take `⟨hex, hinj⟩` from `hS`. Take `⟨e₀, e₁, -, -, h₀, -, -, -, h₀₁, -, -⟩` from `hD R C F`. Use `⟨fun f hf => ?_, fun r hr => ?_⟩` and prove the remaining obligations. Establish `hz` using `h₀₁ f`.

Rewrite `hz` using `[hf, map_zero]`. Take `⟨r, hr⟩` from `(hex (e₀ f)).1 hz.symm`. Use `⟨r, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `c`. Take `⟨T, rfl⟩ : ∃ T, c = ComposableArrows.mk₀ T` from `⟨_, ComposableArrows.ext₀ rfl⟩`.

Use `(h₀ f T).symm.trans ?_` and prove the remaining obligations. Rewrite using `[← hr, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]`. Both sides reduce to the same expression. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Use function extensionality and compare the values at `T`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `congrFun hr (ComposableArrows.mk₀ T)`.
-/
theorem stein_cn : DictSt → ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Stein F → (∀ f : Cn F 0, dn F 0 f = 0 → ∃ r : R, f = r • (1 : Cn F 0)) ∧
      ∀ r : R, r • (1 : Cn F 0) = 0 → r = 0 := by
  intro hD R _ C _ F hS
  obtain ⟨hex, hinj⟩ := hS
  obtain ⟨e₀, e₁, -, -, h₀, -, -, -, h₀₁, -, -⟩ := hD R C F
  refine ⟨fun f hf => ?_, fun r hr => ?_⟩
  · have hz := h₀₁ f
    rw [hf, map_zero] at hz
    obtain ⟨r, hr⟩ := (hex (e₀ f)).1 hz.symm
    refine ⟨r, ?_⟩
    funext c
    obtain ⟨T, rfl⟩ : ∃ T, c = ComposableArrows.mk₀ T := ⟨_, ComposableArrows.ext₀ rfl⟩
    refine (h₀ f T).symm.trans ?_
    rw [← hr, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    rfl
  · apply hinj
    rw [map_zero]
    funext T
    rw [Algebra.algebraMap_eq_smul_one]
    exact congrFun hr (ComposableArrows.mk₀ T)

end GlobalTheory.CompanionTheory.HopfC
