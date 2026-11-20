import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Set `bF` to `fun τ => Module.Basis.ofVectorSpace ℂ (F τ)`. Set `bV` to `fun τ => Module.Basis.ofVectorSpace ℂ (V τ)`. Set `b₁` to `(Basis.piTensorProduct bF).tensorProduct (Basis.piTensorProduct bV)`. Set `b₂` to `Basis.piTensorProduct (fun τ => (bF τ).tensorProduct (bV τ))`. Set `Φ : ((⨂[ℂ] τ, F τ) ⊗[ℂ] (⨂[ℂ] τ, V τ)) →ₗ[ℂ] (⨂[ℂ] τ, (F τ ⊗[ℂ] V τ))` to `TensorProduct.lift (PiTensorProduct.map₂ (fun τ => TensorProduct.mk ℂ (F τ) (V τ)))`.

Establish `hΦ : ∀ (f : ∀ τ, F τ) (v : ∀ τ, V τ), Φ (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (fun τ => f τ ⊗ₜ[ℂ] v τ)`. Introduce `f v`. Simplify using `only [Φ, TensorProduct.lift.tmul, PiTensorProduct.map₂_tprod_tprod, TensorProduct.mk_apply]`. Set `e` to `b₁.equiv b₂ (Equiv.arrowProdEquivProdArrow ι _ _).symm`. Establish `he : (e : _ →ₗ[ℂ] _) = Φ`.

Use `b₁.ext (fun i => ?_)` and prove the remaining obligations. Take `⟨p, q⟩` from `i`. Rewrite using `[LinearEquiv.coe_coe, Module.Basis.equiv_apply]`. Simplify using `only [b₁, b₂, Module.Basis.tensorProduct_apply, Basis.piTensorProduct_apply, hΦ]`. Use `congr 1`.

Use function extensionality and compare the values at `τ`. Conclude with `Module.Basis.tensorProduct_apply' (bF τ) (bV τ) (p τ, q τ)`. Conclude with `⟨e, fun f v => (LinearMap.congr_fun he _).trans (hΦ f v)⟩`.
-/
theorem exists_piTensor_shuffle_equiv (ι : Type) [Fintype ι] (F V : ι → Type)
    [∀ τ, AddCommGroup (F τ)] [∀ τ, Module ℂ (F τ)] [∀ τ, AddCommGroup (V τ)]
    [∀ τ, Module ℂ (V τ)] :
    ∃ e : ((⨂[ℂ] τ, F τ) ⊗[ℂ] (⨂[ℂ] τ, V τ)) ≃ₗ[ℂ] (⨂[ℂ] τ, (F τ ⊗[ℂ] V τ)),
      ∀ (f : ∀ τ, F τ) (v : ∀ τ, V τ),
        e (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v)
          = PiTensorProduct.tprod ℂ (fun τ => f τ ⊗ₜ[ℂ] v τ) := by
  classical

  let bF := fun τ => Module.Basis.ofVectorSpace ℂ (F τ)
  let bV := fun τ => Module.Basis.ofVectorSpace ℂ (V τ)
  let b₁ := (Basis.piTensorProduct bF).tensorProduct (Basis.piTensorProduct bV)
  let b₂ := Basis.piTensorProduct (fun τ => (bF τ).tensorProduct (bV τ))

  let Φ : ((⨂[ℂ] τ, F τ) ⊗[ℂ] (⨂[ℂ] τ, V τ)) →ₗ[ℂ] (⨂[ℂ] τ, (F τ ⊗[ℂ] V τ)) :=
    TensorProduct.lift (PiTensorProduct.map₂ (fun τ => TensorProduct.mk ℂ (F τ) (V τ)))
  have hΦ : ∀ (f : ∀ τ, F τ) (v : ∀ τ, V τ),
      Φ (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v)
        = PiTensorProduct.tprod ℂ (fun τ => f τ ⊗ₜ[ℂ] v τ) := by
    intro f v
    simp only [Φ, TensorProduct.lift.tmul, PiTensorProduct.map₂_tprod_tprod, TensorProduct.mk_apply]

  let e := b₁.equiv b₂ (Equiv.arrowProdEquivProdArrow ι _ _).symm

  have he : (e : _ →ₗ[ℂ] _) = Φ := by
    refine b₁.ext (fun i => ?_)
    obtain ⟨p, q⟩ := i
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp only [b₁, b₂, Module.Basis.tensorProduct_apply, Basis.piTensorProduct_apply, hΦ]
    congr 1
    funext τ
    exact Module.Basis.tensorProduct_apply' (bF τ) (bV τ) (p τ, q τ)
  exact ⟨e, fun f v => (LinearMap.congr_fun he _).trans (hΦ f v)⟩

end GlobalTheory
