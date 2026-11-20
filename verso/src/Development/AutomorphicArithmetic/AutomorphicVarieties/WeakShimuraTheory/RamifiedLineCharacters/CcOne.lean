import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `F Ω _ _ _ _ _`. Establish `key : ∀ w : InfinitePlace F, w.IsReal → ∃ c : G F Ω, IsCCAt w c`. Introduce `w hw`. Establish `hφ : ∀ a, (starRingEnd ℂ) (w.embedding a) = w.embedding a`. Introduce `a`.

Establish `h` using `ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)`. Conclude with `RingHom.congr_fun h a`. Use `letI : Algebra F ℂ := w.embedding.toAlgebra`. Set `e : Ω ≃ₐ[F] algebraicClosure F ℂ` to `IsAlgClosure.equiv F Ω (algebraicClosure F ℂ)`. Set `κ : ℂ →ₐ[F] ℂ` to `{ (starRingEnd ℂ) with commutes' := fun a => hφ a }`.

Set `j : Ω →ₐ[F] ℂ` to `(algebraicClosure F ℂ).val.comp e.toAlgHom`. Establish `hmem : ∀ x : Ω, (κ.comp j) x ∈ (algebraicClosure F ℂ).toSubalgebra`. Introduce `x`. Use `show (κ.comp j) x ∈ algebraicClosure F ℂ`. Rewrite using `[map_mem_algebraicClosure_iff, mem_algebraicClosure_iff]`.

Conclude with `Algebra.IsAlgebraic.isAlgebraic x`. Set `f : Ω →ₐ[F] algebraicClosure F ℂ` to `(κ.comp j).codRestrict _ hmem`. Set `c0 : Ω →ₐ[F] Ω` to `e.symm.toAlgHom.comp f`. Set `c : G F Ω` to `AlgEquiv.ofBijective c0 (Algebra.IsAlgebraic.algHom_bijective c0)`. Use `⟨c, j.toRingHom, fun x => ?_, ?_⟩` and prove the remaining obligations.

Use `show ((e (e.symm (f x)) : algebraicClosure F ℂ) : ℂ) = (starRingEnd ℂ) (j x)`. Rewrite using `[AlgEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Establish `hj : j.toRingHom.comp (algebraMap F Ω) = w.embedding`. Use extensionality with `a`.

Conclude with `j.commutes a`. Rewrite using `[hj, InfinitePlace.mk_embedding]`. Use `⟨fun w => if hw : w.IsReal then (key w hw).choose else 1, fun w hw => ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos hw]`. Conclude with `(key w hw).choose_spec`.
-/
theorem UpperTheory.V.Ws.Gys.ccEx :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ c : InfinitePlace F → G F Ω, ∀ w, w.IsReal → IsCCAt w (c w) := by
  intro F Ω _ _ _ _ _
  classical
  have key : ∀ w : InfinitePlace F, w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
    intro w hw
    have hφ : ∀ a, (starRingEnd ℂ) (w.embedding a) = w.embedding a := by
      intro a
      have h := ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)
      exact RingHom.congr_fun h a
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let e : Ω ≃ₐ[F] algebraicClosure F ℂ := IsAlgClosure.equiv F Ω (algebraicClosure F ℂ)
    let κ : ℂ →ₐ[F] ℂ :=
      { (starRingEnd ℂ) with commutes' := fun a => hφ a }
    let j : Ω →ₐ[F] ℂ := (algebraicClosure F ℂ).val.comp e.toAlgHom
    have hmem : ∀ x : Ω, (κ.comp j) x ∈ (algebraicClosure F ℂ).toSubalgebra := by
      intro x
      show (κ.comp j) x ∈ algebraicClosure F ℂ
      rw [map_mem_algebraicClosure_iff, mem_algebraicClosure_iff]
      exact Algebra.IsAlgebraic.isAlgebraic x
    let f : Ω →ₐ[F] algebraicClosure F ℂ := (κ.comp j).codRestrict _ hmem
    let c0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f
    let c : G F Ω := AlgEquiv.ofBijective c0 (Algebra.IsAlgebraic.algHom_bijective c0)
    refine ⟨c, j.toRingHom, fun x => ?_, ?_⟩
    · show ((e (e.symm (f x)) : algebraicClosure F ℂ) : ℂ) = (starRingEnd ℂ) (j x)
      rw [AlgEquiv.apply_symm_apply]
      rfl
    · have hj : j.toRingHom.comp (algebraMap F Ω) = w.embedding := by
        ext a
        exact j.commutes a
      rw [hj, InfinitePlace.mk_embedding]
  refine ⟨fun w => if hw : w.IsReal then (key w hw).choose else 1, fun w hw => ?_⟩
  simp only [dif_pos hw]
  exact (key w hw).choose_spec
