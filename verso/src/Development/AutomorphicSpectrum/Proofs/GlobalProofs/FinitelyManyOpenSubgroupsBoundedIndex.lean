import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ S hfin N`. Use `haveI : IsGalois F Ω := IsSepClosure.isGalois`. Set `K` to `maxUnramifiedOutside F Ω S`. Set `φ : Subgroup (galUnramifiedOutside F Ω S) → IntermediateField F Ω` to `fun H => IntermediateField.lift (F := K) (IntermediateField.fixedField (H : Subgroup Gal(K/F)))`. Establish `key : ∀ H : Subgroup Gal(K/F), IsOpen (H : Set Gal(K/F)) → (IntermediateField.fixedField H).fixingSubgroup = H` using `fun H hH => InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hH⟩`.

Apply `Set.Finite.of_finite_image (f := φ)` to reduce the goal to its premises. Apply `(hfin N).subset` to reduce the goal to its premises. Introduce and unpack `_ ⟨H, ⟨hHo, -, hHN⟩, rfl⟩`. Establish `hfix` using `key H hHo`. Establish `hfd : FiniteDimensional F (IntermediateField.fixedField (H : Subgroup Gal(K/F)))` using `(InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfix]; exact hHo)`.

Set `e : (IntermediateField.fixedField (H : Subgroup Gal(K/F))) ≃ₐ[F] (φ H)` to `IntermediateField.equivMap _ (IntermediateField.val K)`. Use `haveI : FiniteDimensional F (φ H) := LinearEquiv.finiteDimensional e.toLinearEquiv`. Use `⟨inferInstance, (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 (IntermediateField.lift_le _), ?_⟩` and prove the remaining obligations. Rewrite using `[← e.toLinearEquiv.finrank_eq, IntermediateField.finrank_eq_fixingSubgroup_index, hfix]`. Conclude with `hHN`.

Introduce `H₁ h₁ H₂ h₂ h`. Establish `h'` using `IntermediateField.lift_injective K h`. Conclude with `(key H₁ h₁.1).symm.trans ((congrArg IntermediateField.fixingSubgroup h').trans (key H₂ h₂.1))`.
-/
theorem openSubgroups_finite_of_fields_finite :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Set (HeightOneSpectrum (𝓞 F))),
      (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
        Module.finrank F E ≤ N}.Finite) →
      ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) |
        IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by
  intro F Ω _ _ _ _ _ S hfin N
  haveI : IsGalois F Ω := IsSepClosure.isGalois
  let K := maxUnramifiedOutside F Ω S
  let φ : Subgroup (galUnramifiedOutside F Ω S) → IntermediateField F Ω :=
    fun H => IntermediateField.lift (F := K) (IntermediateField.fixedField (H : Subgroup Gal(K/F)))
  have key : ∀ H : Subgroup Gal(K/F), IsOpen (H : Set Gal(K/F)) →
      (IntermediateField.fixedField H).fixingSubgroup = H := fun H hH =>
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hH⟩
  apply Set.Finite.of_finite_image (f := φ)
  · apply (hfin N).subset
    rintro _ ⟨H, ⟨hHo, -, hHN⟩, rfl⟩
    have hfix := key H hHo
    have hfd : FiniteDimensional F (IntermediateField.fixedField (H : Subgroup Gal(K/F))) :=
      (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfix]; exact hHo)
    let e : (IntermediateField.fixedField (H : Subgroup Gal(K/F))) ≃ₐ[F] (φ H) :=
      IntermediateField.equivMap _ (IntermediateField.val K)
    haveI : FiniteDimensional F (φ H) := LinearEquiv.finiteDimensional e.toLinearEquiv
    refine ⟨inferInstance, (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2
      (IntermediateField.lift_le _), ?_⟩
    rw [← e.toLinearEquiv.finrank_eq, IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    exact hHN
  · intro H₁ h₁ H₂ h₂ h
    have h' := IntermediateField.lift_injective K h
    exact (key H₁ h₁.1).symm.trans ((congrArg IntermediateField.fixingSubgroup h').trans (key H₂ h₂.1))

end GlobalTheory.CompanionTheory.GlobalFiniteness
