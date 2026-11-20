import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BaseChangeIso

/- English proof (translation)
Introduce `R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ e e' f g he he' h`. Establish `hsq : ∀ x : R' ⊗[R] M, e' (liftSemi f x) = liftSemi g (e.lTensor R' x)`. Introduce `x`. Proceed by induction on `x with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul r m => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, h]`. Establish `hb : Function.Bijective (e.lTensor R')`. Use `(TensorProduct.congr (LinearEquiv.refl R R') (LinearEquiv.ofBijective e he)).bijective` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Proceed by induction on `x with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul r m => rfl`.

Establish `hcomp : (⇑e') ∘ (⇑(liftSemi f)) = (⇑(liftSemi g)) ∘ (⇑(e.lTensor R'))` using `funext hsq`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Establish `h1 : Function.Bijective ((⇑e') ∘ (⇑(liftSemi f)))` using `he'.comp hf`. Rewrite `h1` using `[hcomp]`.

Conclude with `(Function.Bijective.of_comp_iff _ hb).mp h1`. Introduce `hg`. Establish `h1 : Function.Bijective ((⇑(liftSemi g)) ∘ (⇑(e.lTensor R')))` using `hg.comp hb`. Rewrite `h1` using `[← hcomp]`. Conclude with `(Function.Bijective.of_comp_iff' he' _).mp h1`.
-/
theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ e e' f g he he' h
  have hsq : ∀ x : R' ⊗[R] M, e' (liftSemi f x) = liftSemi g (e.lTensor R' x) := by
    intro x
    induction x with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r m => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, h]
  have hb : Function.Bijective (e.lTensor R') := by
    have := (TensorProduct.congr (LinearEquiv.refl R R') (LinearEquiv.ofBijective e he)).bijective
    convert this using 1
    funext x
    induction x with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r m => rfl
  have hcomp : (⇑e') ∘ (⇑(liftSemi f)) = (⇑(liftSemi g)) ∘ (⇑(e.lTensor R')) := funext hsq
  constructor
  · intro hf
    have h1 : Function.Bijective ((⇑e') ∘ (⇑(liftSemi f))) := he'.comp hf
    rw [hcomp] at h1
    exact (Function.Bijective.of_comp_iff _ hb).mp h1
  · intro hg
    have h1 : Function.Bijective ((⇑(liftSemi g)) ∘ (⇑(e.lTensor R'))) := hg.comp hb
    rw [← hcomp] at h1
    exact (Function.Bijective.of_comp_iff' he' _).mp h1

end GlobalTheory.BaseChangeIso
