import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPowCompAdicCompletionMapToQuotientPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.InvAlg

open TensorProduct

def galDiff (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] :
    R' →ₗ[R] (GlobalTheory.Mum.Gal (algebraMap R R') → R') :=
  LinearMap.pi fun σ => (galAlg σ).toLinearMap - LinearMap.id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem galDiff_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (x : R')
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) : galDiff R R' x σ = σ.1 x - x := rfl

/- English proof (translation)
Introduce `hinj hgal`. Use `haveI : Finite (GlobalTheory.Mum.Gal (algebraMap R R')) := hgal.1`. Use `haveI : Fintype (GlobalTheory.Mum.Gal (algebraMap R R')) := Fintype.ofFinite _`. Set `incl : R →ₗ[R] R'` to `Algebra.linearMap R R'`. Establish `hex : Function.Exact incl (galDiff R R')`.

Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨r, hr⟩` from `hgal.2 y (fun σ hσ => by`. Use `congrFun hy ⟨σ, hσ⟩` as an intermediate fact.

Rewrite `this` using `[galDiff_apply]`. Simplify `this)` using `[sub_eq_zero]`. Conclude with `⟨r, hr⟩`. Introduce and unpack `⟨r, rfl⟩`. Use function extensionality and compare the values at `σ`.

Simplify using `[incl, galDiff_apply, σ.2 r]`. Establish `hmap : ∀ x : O, LinearMap.lTensor O incl ((TensorProduct.rid R O).symm x) = algebraMap O (TensorProduct R O R') x`. Introduce `x`. Simplify using `[incl, Algebra.TensorProduct.algebraMap_apply]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `a b hab`. Rewrite `hab` using `[← hmap, ← hmap]`. Conclude with `(TensorProduct.rid R O).symm.injective (Module.Flat.lTensor_preserves_injective_linearMap incl hinj hab)`. Introduce `t ht`. Establish `hcomp : ∀ u : TensorProduct R O R', ∀ σ, TensorProduct.piRight R R O (fun _ : GlobalTheory.Mum.Gal (algebraMap R R') => R') (LinearMap.lTensor O (galDiff R R') u) σ = galTensor O σ u - u`.

Introduce `u σ`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`. Rewrite using `[LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]`.

Use `show x ⊗ₜ[R] galDiff R R' y σ = _`. Rewrite using `[galDiff_apply, galTensor_tmul, TensorProduct.tmul_sub]`. Consider the case `add u v hu hv`. Rewrite using `[map_add, map_add, Pi.add_apply, hu, hv, map_add]`. Normalize the expressions using the abelian group laws.

Establish `h0 : LinearMap.lTensor O (galDiff R R') t = 0`. Apply `(TensorProduct.piRight R R O (fun _ : GlobalTheory.Mum.Gal (algebraMap R R') => R')).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `σ`. Rewrite using `[hcomp, ht σ, sub_self, map_zero, Pi.zero_apply]`. Take `⟨y, hy⟩` from `(Module.Flat.lTensor_exact O hex t).1 h0`.

Use `⟨TensorProduct.rid R O y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hmap, LinearEquiv.symm_apply_apply, hy]`.
-/
theorem flat_tensor_invariants (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] [Algebra R O]
    [Module.Flat R O] :
    Function.Injective (algebraMap R R') → GlobalTheory.Mum.IsGal (algebraMap R R') →
    Function.Injective (algebraMap O (TensorProduct R O R')) ∧
    ∀ t : TensorProduct R O R', (∀ σ, GlobalTheory.InvAlg.galTensor O σ t = t) →
      t ∈ Set.range (algebraMap O (TensorProduct R O R')) := by
  intro hinj hgal
  classical
  haveI : Finite (GlobalTheory.Mum.Gal (algebraMap R R')) := hgal.1
  haveI : Fintype (GlobalTheory.Mum.Gal (algebraMap R R')) := Fintype.ofFinite _
  let incl : R →ₗ[R] R' := Algebra.linearMap R R'
  have hex : Function.Exact incl (galDiff R R') := by
    intro y
    constructor
    · intro hy
      obtain ⟨r, hr⟩ := hgal.2 y (fun σ hσ => by
        have := congrFun hy ⟨σ, hσ⟩
        rw [galDiff_apply] at this
        simpa [sub_eq_zero] using this)
      exact ⟨r, hr⟩
    · rintro ⟨r, rfl⟩
      funext σ
      simp [incl, galDiff_apply, σ.2 r]
  have hmap : ∀ x : O, LinearMap.lTensor O incl ((TensorProduct.rid R O).symm x) =
      algebraMap O (TensorProduct R O R') x := by
    intro x
    simp [incl, Algebra.TensorProduct.algebraMap_apply]
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [← hmap, ← hmap] at hab
    exact (TensorProduct.rid R O).symm.injective
      (Module.Flat.lTensor_preserves_injective_linearMap incl hinj hab)
  · intro t ht
    have hcomp : ∀ u : TensorProduct R O R', ∀ σ,
        TensorProduct.piRight R R O (fun _ : GlobalTheory.Mum.Gal (algebraMap R R') => R')
          (LinearMap.lTensor O (galDiff R R') u) σ = galTensor O σ u - u := by
      intro u σ
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        rw [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
        show x ⊗ₜ[R] galDiff R R' y σ = _
        rw [galDiff_apply, galTensor_tmul, TensorProduct.tmul_sub]
      | add u v hu hv =>
        rw [map_add, map_add, Pi.add_apply, hu, hv, map_add]
        abel
    have h0 : LinearMap.lTensor O (galDiff R R') t = 0 := by
      apply (TensorProduct.piRight R R O (fun _ : GlobalTheory.Mum.Gal (algebraMap R R') => R')).injective
      funext σ
      rw [hcomp, ht σ, sub_self, map_zero, Pi.zero_apply]
    obtain ⟨y, hy⟩ := (Module.Flat.lTensor_exact O hex t).1 h0
    refine ⟨TensorProduct.rid R O y, ?_⟩
    rw [← hmap, LinearEquiv.symm_apply_apply, hy]

end GlobalTheory.InvAlg

/- English proof (translation)
The claim follows from `GlobalTheory.InvAlg.flat_tensor_invariants`.
-/
example : ∀ (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] [Algebra R O] [Module.Flat R O],
    Function.Injective (algebraMap R R') → GlobalTheory.Mum.IsGal (algebraMap R R') →
    Function.Injective (algebraMap O (TensorProduct R O R')) ∧
    ∀ t : TensorProduct R O R', (∀ σ, GlobalTheory.InvAlg.galTensor O σ t = t) →
      t ∈ Set.range (algebraMap O (TensorProduct R O R')) := GlobalTheory.InvAlg.flat_tensor_invariants
