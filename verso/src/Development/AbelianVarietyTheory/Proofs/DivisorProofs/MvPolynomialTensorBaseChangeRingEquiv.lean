import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `S B K τ _ _ _ _ _ _ _`. Use `letI : Algebra (MvPolynomial τ S) (MvPolynomial τ B) := MvPolynomial.algebraMvPolynomial`. Set `e : MvPolynomial τ S ⊗[S] B ≃ₐ[MvPolynomial τ S] MvPolynomial τ B` to `Algebra.IsPushout.equiv S (MvPolynomial τ S) B (MvPolynomial τ B)`. Conclude with `⟨(Algebra.TensorProduct.comm (MvPolynomial τ S) (MvPolynomial τ B) K).toRingEquiv.trans ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[MvPolynomial τ S] K) e.symm).toRingEquiv.trans ((Algebra.TensorProduct.cancelBaseChange S (MvPolynomial τ S) (MvPolynomial τ S) K B).toRingE …`.
-/
theorem mvPolynomial_tensor_baseChange_ringEquiv :
    ∀ (S B K τ : Type) [CommRing S] [CommRing B] [CommRing K] [Algebra S B] [Algebra S K]
      [Algebra (MvPolynomial τ S) K] [IsScalarTower S (MvPolynomial τ S) K],
      letI : Algebra (MvPolynomial τ S) (MvPolynomial τ B) :=
        (MvPolynomial.map (algebraMap S B)).toAlgebra
      Nonempty (MvPolynomial τ B ⊗[MvPolynomial τ S] K ≃+* B ⊗[S] K) := by
  intro S B K τ _ _ _ _ _ _ _
  letI : Algebra (MvPolynomial τ S) (MvPolynomial τ B) := MvPolynomial.algebraMvPolynomial
  let e : MvPolynomial τ S ⊗[S] B ≃ₐ[MvPolynomial τ S] MvPolynomial τ B :=
    Algebra.IsPushout.equiv S (MvPolynomial τ S) B (MvPolynomial τ B)
  exact ⟨(Algebra.TensorProduct.comm (MvPolynomial τ S) (MvPolynomial τ B) K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[MvPolynomial τ S] K) e.symm).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange S (MvPolynomial τ S) (MvPolynomial τ S) K B).toRingEquiv.trans
        (Algebra.TensorProduct.comm S K B).toRingEquiv))⟩

end GlobalTheory
