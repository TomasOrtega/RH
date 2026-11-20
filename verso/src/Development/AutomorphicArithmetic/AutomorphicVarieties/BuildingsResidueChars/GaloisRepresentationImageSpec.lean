import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

/- English proof (translation)
Introduce `K M Ω _ _ _ _ _ _ _ _ _ _ _ _`. Use `haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M`. Set `ρ : Gal(Ω/K) →* Gal(M/K)` to `AlgEquiv.restrictNormalHom M`. Establish `hker : (resG K M Ω).range = ρ.ker`. Use extensionality with `σ`.

Rewrite using `[MonoidHom.mem_range, MonoidHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, rfl⟩`. Use extensionality with `x`. Apply `(algebraMap M Ω).injective` to reduce the goal to its premises.

Rewrite using `[show (ρ (resG K M Ω τ)) = (resG K M Ω τ).restrictNormal M from rfl, AlgEquiv.restrictNormal_commutes]`. Simplify using `[resG]`. Introduce `h`. Establish `hfix : ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω x`. Introduce `x`.

Use `AlgEquiv.restrictNormal_commutes σ M x` as an intermediate fact. Rewrite `this` using `[show σ.restrictNormal M = ρ σ from rfl, h]`. Simplify using `using this.symm`. Use `⟨{ σ.toRingEquiv with commutes' := hfix }, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Both sides reduce to the same expression. Use `⟨hker ▸ ρ.normal_ker, ?_⟩` and prove the remaining obligations. Rewrite using `[hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) Ω), Subgroup.card_top, IsGalois.card_aut_eq_finrank]`.
-/
theorem UpperTheory.galois_representation_image_spec :
    UpperTheory.V.Af.Sol.GalRange := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _
  haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
  let ρ : Gal(Ω/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  have hker : (resG K M Ω).range = ρ.ker := by
    ext σ
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨τ, rfl⟩
      ext x
      apply (algebraMap M Ω).injective
      rw [show (ρ (resG K M Ω τ)) = (resG K M Ω τ).restrictNormal M from rfl,
        AlgEquiv.restrictNormal_commutes]
      simp [resG]
    · intro h
      have hfix : ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω x := by
        intro x
        have := AlgEquiv.restrictNormal_commutes σ M x
        rw [show σ.restrictNormal M = ρ σ from rfl, h] at this
        simpa using this.symm
      refine ⟨{ σ.toRingEquiv with commutes' := hfix }, ?_⟩
      ext x
      rfl
  refine ⟨hker ▸ ρ.normal_ker, ?_⟩
  rw [hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) Ω),
    Subgroup.card_top, IsGalois.card_aut_eq_finrank]
