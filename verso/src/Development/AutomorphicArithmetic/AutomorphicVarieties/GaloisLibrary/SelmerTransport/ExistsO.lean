import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.DvrIntClosure

open ReciprocityTheory.Gal UpperTheory.V.Base

/- English proof (translation)
Introduce `l _ n _`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n`. Establish `hζi : IsIntegral ℤ_[l] ζ` using `(hζ.isIntegral (NeZero.pos n)).tower_top`. Set `K : IntermediateField ℚ_[l] (PadicAlgCl l)` to `IntermediateField.adjoin ℚ_[l] {ζ}`. Use `haveI : FiniteDimensional ℚ_[l] K := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)`.

Take `⟨h1, h2, -⟩` from `UpperTheory.V.abelian₂.dvr_intClosure l K`. Set `f : K →ₐ[ℤ_[l]] PadicAlgCl l` to `K.val.restrictScalars ℤ_[l]`. Establish `hf : Function.Injective f` using `Subtype.val_injective`. Set `e` to `(integralClosure ℤ_[l] K).equivMapOfInjective f hf`. Use `⟨(integralClosure ℤ_[l] K).map f, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e`. Conclude with `Module.Finite.equiv e.toLinearEquiv`. Establish `hz : ζ ∈ K` using `IntermediateField.mem_adjoin_simple_self _ _`. Establish `hmem : ζ ∈ (integralClosure ℤ_[l] K).map f` using `⟨⟨ζ, hz⟩, (isIntegral_algHom_iff f hf).1 hζi, rfl⟩`. Use `⟨⟨⟨ζ, hmem⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩` and prove the remaining obligations.

Conclude with `IsPrimitiveRoot.of_map_of_injective (f := ((integralClosure ℤ_[l] K).map f).val) hζ Subtype.val_injective`.
-/
theorem UpperTheory.V.Base.existsO :
    ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) [NeZero n], ∃ O : Subalgebra ℤ_[l] (PadicAlgCl l),
      IsDiscreteValuationRing O ∧ Module.Finite ℤ_[l] O ∧ HasEnoughRootsOfUnity O n := by
  intro l _ n _
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n
  have hζi : IsIntegral ℤ_[l] ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] {ζ}
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨(integralClosure ℤ_[l] K).map f, ?_, ?_, ?_⟩
  · exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  · exact Module.Finite.equiv e.toLinearEquiv
  · have hz : ζ ∈ K := IntermediateField.mem_adjoin_simple_self _ _
    have hmem : ζ ∈ (integralClosure ℤ_[l] K).map f :=
      ⟨⟨ζ, hz⟩, (isIntegral_algHom_iff f hf).1 hζi, rfl⟩
    refine ⟨⟨⟨ζ, hmem⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩
    exact IsPrimitiveRoot.of_map_of_injective (f := ((integralClosure ℤ_[l] K).map f).val) hζ Subtype.val_injective
