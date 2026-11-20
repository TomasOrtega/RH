import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FiniteComplete

/- English proof (translation)
Introduce `O M _ _ _ hO _ _ _`. Use `set I := IsLocalRing.maximalIdeal O`. Establish `hb : Function.Bijective (AdicCompletion.of I O)` using `AdicCompletion.of_bijective_iff.2 hO`. Set `φ : O ≃ₗ[O] AdicCompletion I O` to `LinearEquiv.ofBijective (AdicCompletion.of I O) hb`. Set `e : M ≃ₗ[O] AdicCompletion I O ⊗[O] M` to `(TensorProduct.lid O M).symm.trans (TensorProduct.congr φ (LinearEquiv.refl O M))`.

Establish `h1 : AdicCompletion.of I O 1 = 1`. Use extensionality with `n`. Simplify using the standard rewrite rules. Establish `hfac : ⇑(AdicCompletion.of I M) = ⇑(AdicCompletion.ofTensorProduct I M) ∘ ⇑e`. Use function extensionality and compare the values at `m`.

Establish `he : e m = (1 : AdicCompletion I O) ⊗ₜ[O] m`. Simplify using `[e, φ, h1]`. Simplify using `[he]`. Use `AdicCompletion.of_bijective_iff.1 ?_` and prove the remaining obligations. Rewrite using `[hfac]`.

Conclude with `(AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M).comp e.bijective`.
-/
theorem isAdicComplete_of_finite : ∀ (O M : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [AddCommGroup M] [Module O M]
    [Module.Finite O M], IsAdicComplete (IsLocalRing.maximalIdeal O) M := by
  intro O M _ _ _ hO _ _ _
  set I := IsLocalRing.maximalIdeal O
  have hb : Function.Bijective (AdicCompletion.of I O) := AdicCompletion.of_bijective_iff.2 hO
  let φ : O ≃ₗ[O] AdicCompletion I O := LinearEquiv.ofBijective (AdicCompletion.of I O) hb
  let e : M ≃ₗ[O] AdicCompletion I O ⊗[O] M :=
    (TensorProduct.lid O M).symm.trans (TensorProduct.congr φ (LinearEquiv.refl O M))
  have h1 : AdicCompletion.of I O 1 = 1 := by
    ext n
    simp
  have hfac : ⇑(AdicCompletion.of I M) = ⇑(AdicCompletion.ofTensorProduct I M) ∘ ⇑e := by
    funext m
    have he : e m = (1 : AdicCompletion I O) ⊗ₜ[O] m := by
      simp [e, φ, h1]
    simp [he]
  refine AdicCompletion.of_bijective_iff.1 ?_
  rw [hfac]
  exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M).comp e.bijective

end GlobalTheory.CompanionTheory.FiniteComplete
