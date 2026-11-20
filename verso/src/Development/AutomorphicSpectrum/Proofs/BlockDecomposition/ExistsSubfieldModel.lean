import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace GlobalTheory.CompanionTheory.FieldModel

/- English proof (translation)
Introduce `F Ω _ _ _ _ _`. Set `σ : F →ₐ[ℚ] AlgebraicClosure ℚ` to `IsAlgClosed.lift`. Set `e : F ≃ₐ[ℚ] σ.fieldRange` to `AlgEquiv.ofInjectiveField σ`. Use `haveI fd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional`. Use `haveI nf : NumberField σ.fieldRange := { to_charZero := inferInstance, to_finiteDimensional := fd }`.

Use `haveI alg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by`. Establish `h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ)` using `(AlgebraicClosure.isAlgebraic ℚ)`. Use `h` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`. Use `haveI ac : IsAlgClosure σ.fieldRange (AlgebraicClosure ℚ) := ⟨AlgebraicClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) σ.fieldRange⟩`.

Use `⟨σ.fieldRange, nf, ac, e.toRingEquiv, IsAlgClosure.equivOfEquiv Ω (AlgebraicClosure ℚ) e.toRingEquiv, fun x => ?_⟩` and prove the remaining obligations. Conclude with `IsAlgClosure.equivOfEquiv_algebraMap Ω (AlgebraicClosure ℚ) e.toRingEquiv x`.
-/
theorem exists_subfield_model : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField K) (_ : IsAlgClosure K (AlgebraicClosure ℚ)) (e : F ≃+* K) (E : Ω ≃+* (AlgebraicClosure ℚ)), ∀ x : F, E (algebraMap F Ω x) = algebraMap K (AlgebraicClosure ℚ) (e x) := by
  intro F Ω _ _ _ _ _
  let σ : F →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let e : F ≃ₐ[ℚ] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  haveI fd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional
  haveI nf : NumberField σ.fieldRange := { to_charZero := inferInstance, to_finiteDimensional := fd }
  haveI alg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      (AlgebraicClosure.isAlgebraic ℚ)
    convert h
    exact Subsingleton.elim _ _
  haveI ac : IsAlgClosure σ.fieldRange (AlgebraicClosure ℚ) :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) σ.fieldRange⟩
  refine ⟨σ.fieldRange, nf, ac, e.toRingEquiv, IsAlgClosure.equivOfEquiv Ω (AlgebraicClosure ℚ) e.toRingEquiv, fun x => ?_⟩
  exact IsAlgClosure.equivOfEquiv_algebraMap Ω (AlgebraicClosure ℚ) e.toRingEquiv x

end GlobalTheory.CompanionTheory.FieldModel
