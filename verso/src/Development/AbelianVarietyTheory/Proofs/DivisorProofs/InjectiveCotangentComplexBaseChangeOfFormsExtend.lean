import Mathlib
open TensorProduct KaehlerDifferential

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem injective_cotangentComplexBaseChange_of_forms_extend : ∀ (A P R K : Type) [CommRing A] [CommRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], (∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i) → Function.Injective (KaehlerDifferential.cotangentComplexBaseChange A R P K) := by
  intro A P R K _ _ _ _ _ _ _ _ _ _ _ _ _ hext
  rw [injective_iff_map_eq_zero]
  intro z hz
  refine (Module.forall_dual_apply_eq_zero_iff K z).1 fun φ => ?_
  let ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K :=
    (φ.restrictScalars P) ∘ₗ (TensorProduct.mk P K (RingHom.ker (algebraMap P R)) 1)
  obtain ⟨D, hD⟩ := hext ℓ
  let Λ : K ⊗[P] Ω[P⁄A] →ₗ[K] K := LinearMap.liftBaseChange K D.liftKaehlerDifferential
  have key : Λ ∘ₗ cotangentComplexBaseChange A R P K = φ := by
    ext i
    simp [Λ, cotangentComplexBaseChange_tmul, kerToTensor_apply, hD, ℓ]
  have h2 := congrArg (fun f => f z) key
  simpa [hz] using h2.symm

end GlobalTheory
