import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ w hw`. Set `φ : F →+* ℂ` to `w.embedding`. Establish `hreal : ∀ x : F, starRingEnd ℂ (φ x) = φ x`. Introduce `x`. Establish `h` using `congrArg (fun ψ : F →+* ℂ => ψ x) (NumberField.ComplexEmbedding.isReal_iff.mp (NumberField.InfinitePlace.isReal_iff.mp hw))`.

Simplify using `using h`. Use `letI : Algebra F ℂ := φ.toAlgebra`. Establish `halg : ∀ x : F, algebraMap F ℂ x = φ x` using `fun x => rfl`. Use `haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic`. Use `haveI : Normal F Ω := IsAlgClosure.normal F Ω`.

Set `j : Ω →ₐ[F] ℂ` to `IsAlgClosed.lift`. Set `E : IntermediateField F ℂ` to `j.fieldRange`. Set `e : Ω ≃ₐ[F] E` to `AlgEquiv.ofInjectiveField j`. Use `haveI : Normal F E := Normal.of_algEquiv e`. Set `cj : ℂ →ₐ[F] ℂ` to `{ (starRingEnd ℂ : ℂ →+* ℂ) with commutes' := fun x => by show starRingEnd ℂ (algebraMap F ℂ x) = algebraMap F ℂ x`.

Rewrite using `[halg]`. Conclude with `hreal x }`. Establish `hrange : (cj.comp E.val).fieldRange = E` using `AlgHom.fieldRange_of_normal _`. Establish `hmem : ∀ y : Ω, starRingEnd ℂ (j y) ∈ E`. Introduce `y`.

Establish `h1 : (cj.comp E.val) (e y) ∈ (cj.comp E.val).fieldRange` using `AlgHom.mem_fieldRange.mpr ⟨e y, rfl⟩`. Rewrite `h1` using `[hrange]`. Establish `h2 : ((e y : E) : ℂ) = j y` using `rfl`. Simplify `h1` using `[cj, h2]`. Set `f' : Ω →ₐ[F] E` to `(cj.comp j).codRestrict E.toSubalgebra (fun y => hmem y)`.

Set `σ0 : Ω →ₐ[F] Ω` to `e.symm.toAlgHom.comp f'`. Establish `hbij : Function.Bijective σ0` using `Algebra.IsAlgebraic.algHom_bijective σ0`. Set `c : Ω ≃ₐ[F] Ω` to `AlgEquiv.ofBijective σ0 hbij`. Use `⟨c, (j : Ω →+* ℂ), ?_, ?_⟩` and prove the remaining obligations. Introduce `x`.

Establish `h3 : ((e (e.symm (f' x)) : E) : ℂ) = j (e.symm (f' x))` using `rfl`. Rewrite `h3` using `[AlgEquiv.apply_symm_apply]`. Use `show j (e.symm (f' x)) = starRingEnd ℂ (j x)`. Rewrite using `[← h3]`. Both sides reduce to the same expression.

Establish `h4 : (j : Ω →+* ℂ).comp (algebraMap F Ω) = φ`. Use extensionality with `x`. Simplify using `[halg]`. Rewrite using `[h4]`. Conclude with `NumberField.InfinitePlace.mk_embedding w`.
-/
theorem UpperTheory.V.Ws.exists_complexConjugation_at_realPlace :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : InfinitePlace F), w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
  intro F Ω _ _ _ _ _ w hw
  let φ : F →+* ℂ := w.embedding
  have hreal : ∀ x : F, starRingEnd ℂ (φ x) = φ x := by
    intro x
    have h := congrArg (fun ψ : F →+* ℂ => ψ x)
      (NumberField.ComplexEmbedding.isReal_iff.mp (NumberField.InfinitePlace.isReal_iff.mp hw))
    simpa using h
  letI : Algebra F ℂ := φ.toAlgebra
  have halg : ∀ x : F, algebraMap F ℂ x = φ x := fun x => rfl
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  let j : Ω →ₐ[F] ℂ := IsAlgClosed.lift
  let E : IntermediateField F ℂ := j.fieldRange
  let e : Ω ≃ₐ[F] E := AlgEquiv.ofInjectiveField j
  haveI : Normal F E := Normal.of_algEquiv e
  let cj : ℂ →ₐ[F] ℂ :=
    { (starRingEnd ℂ : ℂ →+* ℂ) with
      commutes' := fun x => by
        show starRingEnd ℂ (algebraMap F ℂ x) = algebraMap F ℂ x
        rw [halg]; exact hreal x }
  have hrange : (cj.comp E.val).fieldRange = E := AlgHom.fieldRange_of_normal _
  have hmem : ∀ y : Ω, starRingEnd ℂ (j y) ∈ E := by
    intro y
    have h1 : (cj.comp E.val) (e y) ∈ (cj.comp E.val).fieldRange := AlgHom.mem_fieldRange.mpr ⟨e y, rfl⟩
    rw [hrange] at h1
    have h2 : ((e y : E) : ℂ) = j y := rfl
    simpa [cj, h2] using h1
  let f' : Ω →ₐ[F] E := (cj.comp j).codRestrict E.toSubalgebra (fun y => hmem y)
  let σ0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f'
  have hbij : Function.Bijective σ0 := Algebra.IsAlgebraic.algHom_bijective σ0
  let c : Ω ≃ₐ[F] Ω := AlgEquiv.ofBijective σ0 hbij
  refine ⟨c, (j : Ω →+* ℂ), ?_, ?_⟩
  · intro x
    have h3 : ((e (e.symm (f' x)) : E) : ℂ) = j (e.symm (f' x)) := rfl
    rw [AlgEquiv.apply_symm_apply] at h3
    show j (e.symm (f' x)) = starRingEnd ℂ (j x)
    rw [← h3]
    rfl
  · have h4 : (j : Ω →+* ℂ).comp (algebraMap F Ω) = φ := by
      ext x
      simp [halg]
    rw [h4]
    exact NumberField.InfinitePlace.mk_embedding w
