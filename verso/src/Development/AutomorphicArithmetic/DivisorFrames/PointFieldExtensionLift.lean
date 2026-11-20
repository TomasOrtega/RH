import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad

/- English proof (translation)
Take `⟨t, ht⟩` from `Algebra.FiniteType.out (R := ℚ) (A := A)`. Use `⟨f '' t, t.finite_toSet.image f, fun L hL a => ?_⟩` and prove the remaining obligations. Establish `h : Algebra.adjoin ℚ (t : Set A) ≤ L.toSubalgebra.comap f.toRatAlgHom` using `Algebra.adjoin_le fun x hx => hL ⟨x, hx, rfl⟩`. Conclude with `h (ht ▸ Algebra.mem_top (x := a))`.
-/
private theorem UpperTheory.finiteType_image_finite_generators {A B : Type} [CommRing A] [Algebra ℚ A] [Algebra.FiniteType ℚ A] [Field B]
    [Algebra ℚ B] (f : A →+* B) :
    ∃ s : Set B, s.Finite ∧ ∀ L : IntermediateField ℚ B, s ⊆ L → ∀ a, f a ∈ L := by
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := ℚ) (A := A)
  refine ⟨f '' t, t.finite_toSet.image f, fun L hL a => ?_⟩
  have h : Algebra.adjoin ℚ (t : Set A) ≤ L.toSubalgebra.comap f.toRatAlgHom :=
    Algebra.adjoin_le fun x hx => hL ⟨x, hx, rfl⟩
  exact h (ht ▸ Algebra.mem_top (x := a))

/- English proof (translation)
Introduce `F K _ _ _ _ Y φ p hp ι β`. Set `x0 : Sp Qb` to `IsLocalRing.closedPoint Qb`. Take `⟨U, hU, hxU, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.X.isBasis_affineOpens) (show p x0 ∈ (⊤ : Y.X.Opens) from trivial)`. Establish `hU' : IsAffineOpen U` using `hU`. Establish `hsub : Subsingleton (Sp Qb)` using `inferInstanceAs (Subsingleton (PrimeSpectrum Qb))`.

Establish `h' : Set.range p ⊆ Set.range hU'.fromSpec`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[hU'.range_fromSpec, Subsingleton.elim z x0]`. Conclude with `hxU`. Set `R` to `Γ(Y.X, U)`.

Set `χ : R →+* Qb` to `(Spec.preimage (IsOpenImmersion.lift hU'.fromSpec p h')).hom`. Establish `hχ : spMap χ ≫ hU'.fromSpec = p` using `(congrArg (· ≫ hU'.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)`. Set `ψ : CommRingCat.of F ⟶ R` to `Spec.preimage (hU'.fromSpec ≫ Y.str)`. Establish `hψ : Spec.map ψ = hU'.fromSpec ≫ Y.str` using `Spec.map_preimage _`. Establish `hY : LocallyOfFiniteType Y.str`.

Establish `h1 : SmoothOfRelativeDimension Y.dim Y.str` using `Y.4`. Establish `: Smooth Y.str` using `SmoothOfRelativeDimension.smooth Y.dim Y.str`. Use `infer_instance`. Establish `hft : LocallyOfFiniteType (Spec.map ψ)`. Rewrite using `[hψ]`.

Conclude with `MorphismProperty.comp_mem _ _ _ inferInstance hY`. Establish `hψft : ψ.hom.FiniteType` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft`. Set `_ : Algebra F R` to `ψ.hom.toAlgebra`. Establish `: Algebra.FiniteType F R` using `hψft`. Set `_ : Algebra ℚ R` to `(ψ.hom.comp (algebraMap ℚ F)).toAlgebra`.

Establish `: IsScalarTower ℚ F R` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: Algebra.FiniteType ℚ R` using `Algebra.FiniteType.trans (S := F) inferInstance inferInstance`. Establish `hχψ : χ.comp ψ.hom = φ`. Establish `h1 : Spec.map (ψ ≫ CommRingCat.ofHom χ) = Spec.map (CommRingCat.ofHom φ)`. Use `(Spec.map_comp _ _).trans ?_` and prove the remaining obligations.

Use `(congrArg (Spec.map (CommRingCat.ofHom χ) ≫ ·) hψ).trans ?_` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.str) hχ).trans hp)`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`. Take `⟨s₁, hs₁, H₁⟩` from `UpperTheory.finiteType_image_finite_generators χ`. Take `⟨s₂, hs₂, H₂⟩` from `UpperTheory.finiteType_image_finite_generators ι`.

Set `S : Set Qb` to `insert β (s₁ ∪ s₂)`. Establish `hS : S.Finite` using `(hs₁.union hs₂).insert β`. Establish `: Finite S` using `hS`. Set `L : IntermediateField ℚ Qb` to `IntermediateField.adjoin ℚ S`. Establish `halg : Algebra.IsAlgebraic ℚ Qb` using `algebraicClosure.isAlgebraic ℚ ℂ`.

Establish `hfd : FiniteDimensional ℚ L` using `IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Establish `hSL : S ⊆ L` using `IntermediateField.subset_adjoin ℚ S`. Establish `hnf : NumberField L` using `NumberField.of_module_finite ℚ L`. Establish `m₁` using `H₁ L fun x hx => hSL (Or.inr (Or.inl hx))`. Establish `m₂` using `H₂ L fun x hx => hSL (Or.inr (Or.inr hx))`.

Set `χ' : R →+* L` to `χ.codRestrict L m₁`. Use `⟨L, inferInstance, hnf, L.val.toRingHom, χ'.comp ψ.hom, ι.codRestrict L m₂, ⟨β, hSL (Or.inl rfl)⟩, spMap χ' ≫ hU'.fromSpec, ?_, ?_, rfl, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hχψ]`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Rewrite using `[← hχ, ← Category.assoc]`. Conclude with `congrArg (· ≫ hU'.fromSpec) (Spec.map_comp _ _).symm`. Rewrite using `[Category.assoc, ← hψ]`. Conclude with `(Spec.map_comp _ _).symm`.
-/
theorem UpperTheory.point_field_extension_lift :
    ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] (Y : Var F) (φ : F →+* Qb) (p : Sp Qb ⟶ Y.X), p ≫ Y.str = spMap φ → ∀ (ι : K →+* Qb) (β : Qb), ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (ι' : K' →+* Qb) (φ' : F →+* K') (ρ : K →+* K') (b : K') (q : Sp K' ⟶ Y.X), ι'.comp φ' = φ ∧ ι'.comp ρ = ι ∧ ι' b = β ∧ spMap ι' ≫ q = p ∧ q ≫ Y.str = spMap φ' := by
  intro F K _ _ _ _ Y φ p hp ι β
  let x0 : Sp Qb := IsLocalRing.closedPoint Qb
  obtain ⟨U, hU, hxU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.X.isBasis_affineOpens) (show p x0 ∈ (⊤ : Y.X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hsub : Subsingleton (Sp Qb) := inferInstanceAs (Subsingleton (PrimeSpectrum Qb))
  have h' : Set.range p ⊆ Set.range hU'.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hU'.range_fromSpec, Subsingleton.elim z x0]
    exact hxU
  let R := Γ(Y.X, U)
  let χ : R →+* Qb := (Spec.preimage (IsOpenImmersion.lift hU'.fromSpec p h')).hom
  have hχ : spMap χ ≫ hU'.fromSpec = p :=
    (congrArg (· ≫ hU'.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)
  let ψ : CommRingCat.of F ⟶ R := Spec.preimage (hU'.fromSpec ≫ Y.str)
  have hψ : Spec.map ψ = hU'.fromSpec ≫ Y.str := Spec.map_preimage _
  have hY : LocallyOfFiniteType Y.str := by
    have h1 : SmoothOfRelativeDimension Y.dim Y.str := Y.4
    have : Smooth Y.str := SmoothOfRelativeDimension.smooth Y.dim Y.str
    infer_instance
  have hft : LocallyOfFiniteType (Spec.map ψ) := by
    rw [hψ]; exact MorphismProperty.comp_mem _ _ _ inferInstance hY
  have hψft : ψ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  let _ : Algebra F R := ψ.hom.toAlgebra
  have : Algebra.FiniteType F R := hψft
  let _ : Algebra ℚ R := (ψ.hom.comp (algebraMap ℚ F)).toAlgebra
  have : IsScalarTower ℚ F R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType ℚ R := Algebra.FiniteType.trans (S := F) inferInstance inferInstance
  have hχψ : χ.comp ψ.hom = φ := by
    have h1 : Spec.map (ψ ≫ CommRingCat.ofHom χ) = Spec.map (CommRingCat.ofHom φ) := by
      refine (Spec.map_comp _ _).trans ?_
      refine (congrArg (Spec.map (CommRingCat.ofHom χ) ≫ ·) hψ).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.str) hχ).trans hp)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  obtain ⟨s₁, hs₁, H₁⟩ := UpperTheory.finiteType_image_finite_generators χ
  obtain ⟨s₂, hs₂, H₂⟩ := UpperTheory.finiteType_image_finite_generators ι
  let S : Set Qb := insert β (s₁ ∪ s₂)
  have hS : S.Finite := (hs₁.union hs₂).insert β
  have : Finite S := hS
  let L : IntermediateField ℚ Qb := IntermediateField.adjoin ℚ S
  have halg : Algebra.IsAlgebraic ℚ Qb := algebraicClosure.isAlgebraic ℚ ℂ
  have hfd : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hSL : S ⊆ L := IntermediateField.subset_adjoin ℚ S
  have hnf : NumberField L := NumberField.of_module_finite ℚ L
  have m₁ := H₁ L fun x hx => hSL (Or.inr (Or.inl hx))
  have m₂ := H₂ L fun x hx => hSL (Or.inr (Or.inr hx))
  let χ' : R →+* L := χ.codRestrict L m₁
  refine ⟨L, inferInstance, hnf, L.val.toRingHom, χ'.comp ψ.hom, ι.codRestrict L m₂, ⟨β, hSL (Or.inl rfl)⟩,
    spMap χ' ≫ hU'.fromSpec, ?_, ?_, rfl, ?_, ?_⟩
  · rw [← hχψ]; rfl
  · rfl
  · rw [← hχ, ← Category.assoc]
    exact congrArg (· ≫ hU'.fromSpec) (Spec.map_comp _ _).symm
  · rw [Category.assoc, ← hψ]
    exact (Spec.map_comp _ _).symm
