import Mathlib

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.FiniteSeparablePoints

/- English proof (translation)
Set `R : Subalgebra k Ω` to `φ.range`. Establish `hsurj : Function.Surjective φ.rangeRestrict` using `φ.rangeRestrict_surjective`. Establish `: Algebra.FiniteType k R` using `Algebra.FiniteType.of_surjective φ.rangeRestrict hsurj`. Establish `: Algebra.FormallyUnramified k R` using `Algebra.FormallyUnramified.of_surjective φ.rangeRestrict hsurj`. Establish `: Module.Finite k R` using `Algebra.FormallyUnramified.finite_of_free k R`.

Establish `hF : IsField R` using `isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)`. Set `K : IntermediateField k Ω` to `R.toIntermediateField' hF`. Establish `hmem : ∀ x, φ x ∈ K.toSubalgebra` using `fun x => ⟨x, rfl⟩`. Set `ψ : S →ₐ[k] K` to `φ.codRestrict K.toSubalgebra hmem`. Establish `hψ : Function.Surjective ψ`.

Introduce and unpack `⟨y, x, rfl⟩`. Conclude with `⟨x, rfl⟩`. Establish `: Algebra.FiniteType k K` using `Algebra.FiniteType.of_surjective ψ hψ`. Establish `: Algebra.FormallyUnramified k K` using `Algebra.FormallyUnramified.of_surjective ψ hψ`. Establish `: Module.Finite k K` using `Algebra.FormallyUnramified.finite_of_free k K`.

Use `⟨K, inferInstance, (Algebra.FormallyUnramified.iff_isSeparable k K).1 inferInstance, ψ.toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Both sides reduce to the same expression.
-/
theorem exists_factor_of_unramified {k Ω S : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing S]
    [Algebra k S] [Algebra.FormallyUnramified k S] [Algebra.FiniteType k S] (φ : S →ₐ[k] Ω) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ ψ : S →+* K, (algebraMap K Ω).comp ψ = φ.toRingHom := by
  classical
  let R : Subalgebra k Ω := φ.range
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have : Algebra.FiniteType k R := Algebra.FiniteType.of_surjective φ.rangeRestrict hsurj
  have : Algebra.FormallyUnramified k R := Algebra.FormallyUnramified.of_surjective φ.rangeRestrict hsurj
  have : Module.Finite k R := Algebra.FormallyUnramified.finite_of_free k R
  have hF : IsField R := isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)
  let K : IntermediateField k Ω := R.toIntermediateField' hF
  have hmem : ∀ x, φ x ∈ K.toSubalgebra := fun x => ⟨x, rfl⟩
  let ψ : S →ₐ[k] K := φ.codRestrict K.toSubalgebra hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have : Algebra.FiniteType k K := Algebra.FiniteType.of_surjective ψ hψ
  have : Algebra.FormallyUnramified k K := Algebra.FormallyUnramified.of_surjective ψ hψ
  have : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
  refine ⟨K, inferInstance, (Algebra.FormallyUnramified.iff_isSeparable k K).1 inferInstance,
    ψ.toRingHom, ?_⟩
  ext x
  rfl

/- English proof (translation)
Take `⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω))` from `inferInstance`. Take `⟨_, ⟨U, hU0, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (a pt)) isOpen_univ`. Establish `hU : IsAffineOpen U` using `hU0`. Establish `hrange : Set.range a ⊆ Set.range hU.fromSpec`. Rewrite using `[hU.range_fromSpec]`.

Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Subsingleton.elim y pt]` and apply the resulting hypothesis. Establish `hca : IsOpenImmersion.lift hU.fromSpec a hrange ≫ hU.fromSpec = a` using `IsOpenImmersion.lift_fac _ _ _`. Take `⟨f, hf⟩ : ∃ f, Spec.map f = IsOpenImmersion.lift hU.fromSpec a hrange` from `⟨_, Spec.map_preimage _⟩`. Take `⟨g, hg⟩ : ∃ g, Spec.map g = hU.fromSpec ≫ p` from `⟨_, Spec.map_preimage _⟩`.

Establish `hgf : g ≫ f = CommRingCat.ofHom (algebraMap k Ω)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hf, hg, ← Category.assoc, hca, h]`. Establish `hU1 : RingHom.FormallyUnramified g.hom`. Rewrite using `[← HasRingHomProperty.Spec_iff (P := @FormallyUnramified), hg]`.

Conclude with `HasRingHomProperty.comp_of_isOpenImmersion @FormallyUnramified hU.fromSpec p ‹_›`. Establish `hU2 : RingHom.FiniteType g.hom`. Rewrite using `[← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hg]`. Use `infer_instance`. Set `_ : Algebra k Γ(X, U)` to `g.hom.toAlgebra`.

Establish `: Algebra.FormallyUnramified k Γ(X, U)` using `hU1`. Establish `: Algebra.FiniteType k Γ(X, U)` using `hU2`. Set `φ' : Γ(X, U) →ₐ[k] Ω` to `{ f.hom with commutes' := fun r => by`. Establish `e` using `congrArg (fun q => q.hom r) hgf`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e`.

Conclude with `e }`. Take `⟨K, hK1, hK2, ψ, hψ⟩` from `exists_factor_of_unramified φ'`. Use `⟨K, hK1, hK2, Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩` and prove the remaining obligations. Establish `e : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap K Ω) = f`. Use extensionality with `x`.

Conclude with `congrArg (fun q => q x) hψ`. Rewrite using `[← Category.assoc, ← Spec.map_comp, e, hf, hca]`.
-/
theorem exists_finite_separable_point {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {X : Scheme} (p : X ⟶ Spec (CommRingCat.of k)) [FormallyUnramified p]
    [LocallyOfFiniteType p] (a : Spec (CommRingCat.of Ω) ⟶ X)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = a := by
  classical
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨_, ⟨U, hU0, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (a pt)) isOpen_univ
  have hU : IsAffineOpen U := hU0
  have hrange : Set.range a ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y pt]
  have hca : IsOpenImmersion.lift hU.fromSpec a hrange ≫ hU.fromSpec = a :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨f, hf⟩ : ∃ f, Spec.map f = IsOpenImmersion.lift hU.fromSpec a hrange :=
    ⟨_, Spec.map_preimage _⟩
  obtain ⟨g, hg⟩ : ∃ g, Spec.map g = hU.fromSpec ≫ p := ⟨_, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap k Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf, hg, ← Category.assoc, hca, h]
  have hU1 : RingHom.FormallyUnramified g.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @FormallyUnramified), hg]
    exact HasRingHomProperty.comp_of_isOpenImmersion @FormallyUnramified hU.fromSpec p ‹_›
  have hU2 : RingHom.FiniteType g.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hg]
    infer_instance
  let _ : Algebra k Γ(X, U) := g.hom.toAlgebra
  have : Algebra.FormallyUnramified k Γ(X, U) := hU1
  have : Algebra.FiniteType k Γ(X, U) := hU2
  let φ' : Γ(X, U) →ₐ[k] Ω :=
    { f.hom with
      commutes' := fun r => by
        have e := congrArg (fun q => q.hom r) hgf
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
        exact e }
  obtain ⟨K, hK1, hK2, ψ, hψ⟩ := exists_factor_of_unramified φ'
  refine ⟨K, hK1, hK2, Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  have e : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap K Ω) = f := by
    ext x
    exact congrArg (fun q => q x) hψ
  rw [← Category.assoc, ← Spec.map_comp, e, hf, hca]

end GlobalTheory.FiniteSeparablePoints
