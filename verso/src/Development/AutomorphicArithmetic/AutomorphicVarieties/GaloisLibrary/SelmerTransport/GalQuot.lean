import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

/- English proof (translation)
Introduce `k E Ω _ _ _ _ _ _ _ _ _ _ _ _`. Establish `hN : Normal k Ω` using `IsAlgClosure.normal k Ω`. Establish `hc : ∀ (σ : G k Ω) (x : E), σ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormalHom E σ x)`. Introduce `σ x`. Conclude with `(AlgEquiv.restrictNormal_commutes σ E x).symm`.

Use `⟨AlgEquiv.restrictNormalHom_surjective Ω, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `σ`. Rewrite using `[MonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `_ ↔ ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x`. Prove the components needed by the constructor for the conclusion.

Introduce `h x`. Rewrite using `[hc, h]`. Both sides reduce to the same expression. Introduce `h`. Use extensionality with `x`.

Apply `(algebraMap E Ω).injective` to reduce the goal to its premises. Rewrite using `[← hc, h]`. Both sides reduce to the same expression. Introduce `σ x`. Conclude with `hc σ x`.
-/
theorem UpperTheory.V.Base.galQuot :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] [Normal k E],
      Function.Surjective (AlgEquiv.restrictNormalHom E : G k Ω →* (E ≃ₐ[k] E)) ∧
      (AlgEquiv.restrictNormalHom E : G k Ω →* (E ≃ₐ[k] E)).ker = galOf k E Ω ∧
      ∀ σ : G k Ω, IsLift (AlgEquiv.restrictNormalHom E σ : E ≃ₐ[k] E).toRingEquiv σ.toRingEquiv := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _
  have hN : Normal k Ω := IsAlgClosure.normal k Ω
  have hc : ∀ (σ : G k Ω) (x : E),
      σ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormalHom E σ x) := by
    intro σ x
    exact (AlgEquiv.restrictNormal_commutes σ E x).symm
  refine ⟨AlgEquiv.restrictNormalHom_surjective Ω, ?_, ?_⟩
  · ext σ
    rw [MonoidHom.mem_ker]
    change _ ↔ ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x
    constructor
    · intro h x
      rw [hc, h]
      rfl
    · intro h
      ext x
      apply (algebraMap E Ω).injective
      rw [← hc, h]
      rfl
  · intro σ x
    exact hc σ x
