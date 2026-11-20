import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.KerMapPowerSeriesQuotient
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Introduce `O O' B _ _ _ _ _ _ _ Q hQ`. Use `haveI hN : IsNoetherianRing (O' ⊗[O] B) := by`. Use `letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra`. Use `haveI : Module.Finite B (O' ⊗[O] B) := Module.Finite.equiv (Algebra.TensorProduct.commRight O B O').toLinearEquiv`. Conclude with `Algebra.FiniteType.isNoetherianRing B (O' ⊗[O] B)`.

Take `⟨-, -, h3, h4⟩` from `UpperTheory.V.AlgebraTools.powerSeries_ker_map (O' ⊗[O] B) Q (IsNoetherian.noetherian Q)`. Use `⟨h3 hQ, ?_⟩` and prove the remaining obligations. Establish `h5 : (Q.map (Til.C O O' B)).comap (Til.C O O' B) = Q` using `h4`. Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap]`.

Use `conv_rhs => rw [← h5]`. Conclude with `Iff.rfl`.
-/
theorem UpperTheory.V.Pa.BC.til_prime :
    ∀ (O O' B : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [CommRing B] [Algebra O B] [IsNoetherianRing B] (Q : Ideal (O' ⊗[O] B)), Q.IsPrime → (Q.map (Til.C O O' B)).IsPrime ∧ (Q.map (Til.C O O' B)).comap (Til.ι O O' B) = Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) := by
  intro O O' B _ _ _ _ _ _ _ Q hQ
  haveI hN : IsNoetherianRing (O' ⊗[O] B) := by
    letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
    haveI : Module.Finite B (O' ⊗[O] B) :=
      Module.Finite.equiv (Algebra.TensorProduct.commRight O B O').toLinearEquiv
    exact Algebra.FiniteType.isNoetherianRing B (O' ⊗[O] B)
  obtain ⟨-, -, h3, h4⟩ := UpperTheory.V.AlgebraTools.powerSeries_ker_map (O' ⊗[O] B) Q (IsNoetherian.noetherian Q)
  refine ⟨h3 hQ, ?_⟩
  have h5 : (Q.map (Til.C O O' B)).comap (Til.C O O' B) = Q := h4
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  conv_rhs => rw [← h5]
  exact Iff.rfl
