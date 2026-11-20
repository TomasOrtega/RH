import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

namespace GlobalTheory.Desc.FlatLinDisj

/- English proof (translation)
Introduce `n u hu r hr`. Set `f : (Fin n → R) →ₗ[R] K` to `Fintype.linearCombination R u`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `a ha`.

Apply `hu a` to reduce the goal to its premises. Simplify `ha` using `[f, Fintype.linearCombination_apply, Algebra.smul_def]`. Establish `hft : Function.Injective (f.rTensor R₁)` using `Module.Flat.rTensor_preserves_injective_linearMap f hf`. Use `set x : (Fin n → R) ⊗[R] R₁ := ∑ j, Pi.single j 1 ⊗ₜ[R] r j with hx`. Establish `hx0 : x = 0`.

Apply `hft` to reduce the goal to its premises. Rewrite using `[map_zero, hx, map_sum]`. Simplify using `only [LinearMap.rTensor_tmul]`. Use `h n u r hr` as an intermediate fact. Simplify `this` using `[f, Fintype.linearCombination_apply_single]`.

Use function extensionality and compare the values at `i`. Establish `key : TensorProduct.lid R R₁ ((LinearMap.proj (R` using `R) (φ := fun _ : Fin n => R) i).rTensor R₁ x) = r i := by`. Rewrite using `[hx, map_sum, map_sum]`. Simplify using `[LinearMap.rTensor_tmul, Pi.single_apply]`. Rewrite using `[← key, hx0]`.

Simplify using the standard rewrite rules.
-/
theorem linDisj_of_flat (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁]
    [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L)
    (h : ∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) :
    LinDisj (algebraMap R K) c θ := by
  intro n u hu r hr
  let f : (Fin n → R) →ₗ[R] K := Fintype.linearCombination R u
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    apply hu a
    simpa [f, Fintype.linearCombination_apply, Algebra.smul_def] using ha
  have hft : Function.Injective (f.rTensor R₁) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  set x : (Fin n → R) ⊗[R] R₁ := ∑ j, Pi.single j 1 ⊗ₜ[R] r j with hx
  have hx0 : x = 0 := by
    apply hft
    rw [map_zero, hx, map_sum]
    simp only [LinearMap.rTensor_tmul]
    have := h n u r hr
    simpa [f, Fintype.linearCombination_apply_single] using this
  funext i
  have key : TensorProduct.lid R R₁ ((LinearMap.proj (R := R) (φ := fun _ : Fin n => R) i).rTensor R₁ x) = r i := by
    rw [hx, map_sum, map_sum]
    simp [LinearMap.rTensor_tmul, Pi.single_apply]
  rw [← key, hx0]
  simp

end GlobalTheory.Desc.FlatLinDisj
