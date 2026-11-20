import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Introduce `A B _ _ _ _ _ _ _ h`. Take `⟨hN, n, hdim, rs, hlen, hmem, hreg⟩` from `h`. Establish `hinj : Function.Injective (algebraMap A B)` using `FaithfulSMul.algebraMap_injective A B`. Establish `hm : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A` using `eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B))`. Use `⟨IsNoetherianRing.of_finite A B, n, ?_, rs.map (algebraMap A B), by simpa using hlen, ?_, hreg.of_faithfullyFlat⟩` and prove the remaining obligations.

Rewrite using `[← hdim]`. Conclude with `ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj`. Introduce `r hr`. Take `⟨a, ha, rfl⟩` from `List.mem_map.mp hr`. Use `hmem a ha` as an intermediate fact.

Rewrite `this` using `[← hm]`. Conclude with `this`.
-/
theorem UpperTheory.V.AlgebraTools.Conn.cmFree :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Module.Finite A B]
      [Module.Free A B], ReciprocityTheory.CA.IsCM A → ReciprocityTheory.CA.IsCM B := by
  intro A B _ _ _ _ _ _ _ h
  obtain ⟨hN, n, hdim, rs, hlen, hmem, hreg⟩ := h
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hm : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B))
  refine ⟨IsNoetherianRing.of_finite A B, n, ?_, rs.map (algebraMap A B), by simpa using hlen, ?_,
    hreg.of_faithfullyFlat⟩
  · rw [← hdim]
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    have := hmem a ha
    rw [← hm] at this
    exact this
