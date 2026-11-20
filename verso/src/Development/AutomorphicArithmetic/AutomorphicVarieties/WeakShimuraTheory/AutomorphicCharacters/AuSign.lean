import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.auSign :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] (μ : G ℚ Ω →* C) (c c' : G ℚ Ω), Af.IsConjEl c → Af.IsConjEl c' → μ c = μ c' := by
  intro Ω _ _ _ C _ μ c c' hc hc'
  obtain ⟨j, hj⟩ := hc
  obtain ⟨j', hj'⟩ := hc'
  letI : Algebra Ω ℂ := j.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra]
  let σ : Ω ≃ₐ[ℚ] Ω := AlgHom.restrictNormal' j'.toRatAlgHom Ω
  have hσ : ∀ x, j (σ x) = j' x := fun x => by
    have h := AlgHom.restrictNormal_commutes j'.toRatAlgHom Ω x
    simp only [RingHom.algebraMap_toAlgebra, Algebra.algebraMap_self, RingHom.id_apply,
      RingHom.toRatAlgHom_apply] at h
    exact h
  have key : σ * c' = c * σ := by
    ext x
    apply j.injective
    show j (σ (c' x)) = j (c (σ x))
    rw [hσ, hj', hj, hσ]
  have h2 := congrArg μ key
  rw [map_mul, map_mul, mul_comm (μ c) (μ σ)] at h2
  exact (mul_left_cancel h2).symm
