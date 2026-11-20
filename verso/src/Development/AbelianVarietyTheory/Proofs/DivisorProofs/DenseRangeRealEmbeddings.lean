import Development.AbelianVarietyTheory.Definitions.Divisors.IsSimplicial
open NumberField GlobalTheory.Shintani MeasureTheory Filter Topology

namespace GlobalTheory.Shintani

/- English proof (translation)
Introduce `F _ _ _`. Establish `h1` using `NumberField.InfiniteAdeleRing.denseRange_algebraMap F`. Set `E : ∀ w : InfinitePlace F, w.Completion → ℝ` to `fun w z => InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) z`. Establish `hs : Function.Surjective (Pi.map E)`. Introduce `y`.

Use `⟨fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y w), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Conclude with `(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (y w)`. Establish `hc : Continuous (Pi.map E)`. Use `continuous_pi fun w => ?_` and prove the remaining obligations.

Establish `: (E w) = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)`. Use function extensionality and compare the values at `z`. Conclude with `InfinitePlace.Completion.ringEquivRealOfIsReal_apply _ z`. Express the relevant statement in the definitionally equal form `Continuous fun a : (∀ v : InfinitePlace F, v.Completion) => E w (a w)`. Rewrite using `[this]`.

Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)`. Establish `h2` using `hs.denseRange.comp h1 hc`. Set `g : (F →+* ℝ) → InfinitePlace F` to `fun σ => InfinitePlace.mk (Complex.ofRealHom.comp σ)`. Establish `hreal : ∀ σ : F →+* ℝ, ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ)`. Introduce `σ`.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`. Establish `hemb : ∀ σ : F →+* ℝ, (g σ).embedding = Complex.ofRealHom.comp σ` using `fun σ => InfinitePlace.embedding_mk_eq_of_isReal (hreal σ)`. Establish `hg : Function.Injective g`.

Introduce `σ τ h`. Use `hemb σ` as an intermediate fact. Rewrite `this` using `[h, hemb τ]`. Use extensionality with `x`. Establish `h3` using `congrArg (fun f : F →+* ℂ => f x) this`.

Simplify using `only [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_inj] at h3`. Conclude with `h3.symm`. Establish `hval : ∀ (x : F) (σ : F →+* ℝ), Pi.map E (algebraMap F (InfiniteAdeleRing F) x) (g σ) = σ x`. Introduce `x σ`. Express the relevant statement in the definitionally equal form `E (g σ) (algebraMap F (InfiniteAdeleRing F) x (g σ)) = σ x`.

Rewrite using `[InfiniteAdeleRing.algebraMap_apply]`. Establish `e1` using `InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal (g σ)) ((WithAbs.equiv (g σ).1).symm x)`. Establish `e2` using `InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal (g σ)) x`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Simplify using `only [E, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]`.

Establish `e3 : ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal (g σ))) { toCompletion` using `↑(WithAbs.toAbs (g σ).1 x) } : ℂ) = (g σ).embedding x := by`. Rewrite using `[← e2]`. Simplify using `only [RingEquiv.apply_symm_apply, WithAbs.equiv_symm_apply, WithAbs.equiv_apply] at e1`. Conclude with `congrArg _ e1`. Rewrite using `[e3, hemb σ]`.

Both sides reduce to the same expression. Set `P : (InfinitePlace F → ℝ) → ((F →+* ℝ) → ℝ)` to `fun y σ => y (g σ)`. Establish `hPs : Function.Surjective P` using `fun z => ⟨Function.extend g z 0, funext fun σ => hg.extend_apply z 0 σ⟩`. Establish `hPc : Continuous P` using `continuous_pi fun σ => continuous_apply (g σ)`. Use `hPs.denseRange.comp h2 hPc using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x σ`. Conclude with `(hval x σ).symm`.
-/
theorem denseRange_realEmbeddings :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
      DenseRange (fun (x : F) (σ : F →+* ℝ) => σ x) := by
  intro F _ _ _
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  let E : ∀ w : InfinitePlace F, w.Completion → ℝ := fun w z =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) z
  have hs : Function.Surjective (Pi.map E) := by
    intro y
    refine ⟨fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y w), ?_⟩
    funext w
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (y w)
  have hc : Continuous (Pi.map E) := by
    refine continuous_pi fun w => ?_
    have : (E w) = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) := by
      funext z; exact InfinitePlace.Completion.ringEquivRealOfIsReal_apply _ z
    change Continuous fun a : (∀ v : InfinitePlace F, v.Completion) => E w (a w)
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  have h2 := hs.denseRange.comp h1 hc
  let g : (F →+* ℝ) → InfinitePlace F := fun σ => InfinitePlace.mk (Complex.ofRealHom.comp σ)
  have hreal : ∀ σ : F →+* ℝ, ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    intro σ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hemb : ∀ σ : F →+* ℝ, (g σ).embedding = Complex.ofRealHom.comp σ := fun σ =>
    InfinitePlace.embedding_mk_eq_of_isReal (hreal σ)
  have hg : Function.Injective g := by
    intro σ τ h
    have := hemb σ
    rw [h, hemb τ] at this
    ext x
    have h3 := congrArg (fun f : F →+* ℂ => f x) this
    simp only [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_inj] at h3
    exact h3.symm
  have hval : ∀ (x : F) (σ : F →+* ℝ), Pi.map E (algebraMap F (InfiniteAdeleRing F) x) (g σ) = σ x := by
    intro x σ
    change E (g σ) (algebraMap F (InfiniteAdeleRing F) x (g σ)) = σ x
    rw [InfiniteAdeleRing.algebraMap_apply]
    have e1 := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal (g σ))
      ((WithAbs.equiv (g σ).1).symm x)
    have e2 := InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal (g σ)) x
    apply Complex.ofReal_injective
    simp only [E, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    have e3 : ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal (g σ)))
        { toCompletion := ↑(WithAbs.toAbs (g σ).1 x) } : ℂ) = (g σ).embedding x := by
      rw [← e2]
      simp only [RingEquiv.apply_symm_apply, WithAbs.equiv_symm_apply, WithAbs.equiv_apply] at e1
      exact congrArg _ e1
    rw [e3, hemb σ]
    rfl

  let P : (InfinitePlace F → ℝ) → ((F →+* ℝ) → ℝ) := fun y σ => y (g σ)
  have hPs : Function.Surjective P := fun z => ⟨Function.extend g z 0, funext fun σ => hg.extend_apply z 0 σ⟩
  have hPc : Continuous P := continuous_pi fun σ => continuous_apply (g σ)
  convert hPs.denseRange.comp h2 hPc using 1
  funext x σ
  exact (hval x σ).symm

end GlobalTheory.Shintani
