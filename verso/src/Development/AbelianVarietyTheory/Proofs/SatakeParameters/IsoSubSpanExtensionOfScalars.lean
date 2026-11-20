import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

/- English proof (translation)
Introduce `k Γ _ _ L _ f a ρ W₁ W₂ h₁ h₂ ⟨e, he⟩`. Take `⟨g₁, hg₁⟩` from `LinearMap.exists_extend (W₂.subtype ∘ₗ (e : W₁ →ₗ[k] W₂))`. Take `⟨g₂, hg₂⟩` from `LinearMap.exists_extend (W₁.subtype ∘ₗ (e.symm : W₂ →ₗ[k] W₁))`. Establish `hg₁' : ∀ v : W₁, g₁ v = (e v : Fin a → k)` using `fun v => by`. Simplify using `using LinearMap.congr_fun hg₁ v`.

Establish `hg₂' : ∀ v : W₂, g₂ v = (e.symm v : Fin a → k)` using `fun v => by`. Simplify using `using LinearMap.congr_fun hg₂ v`. Establish `key : ∀ (M : Matrix (Fin a) (Fin a) k) (v : Fin a → k), (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v)`. Introduce `M v`. Use function extensionality and compare the values at `i`.

Conclude with `(RingHom.map_mulVec f M v i).symm`. Set `φ : (Fin a → L) →ₗ[L] (Fin a → L)` to `((LinearMap.toMatrix' g₁).map f).mulVecLin`. Set `ψ : (Fin a → L) →ₗ[L] (Fin a → L)` to `((LinearMap.toMatrix' g₂).map f).mulVecLin`. Establish `hφ : ∀ w (hw : w ∈ W₁), φ (f ∘ w) = f ∘ (e ⟨w, hw⟩ : Fin a → k)`. Introduce `w hw`.

Use `show ((LinearMap.toMatrix' g₁).map f).mulVec (f ∘ w) = _`. Rewrite using `[key, LinearMap.toMatrix'_mulVec]`. Conclude with `congrArg _ (hg₁' ⟨w, hw⟩)`. Establish `hψ : ∀ w (hw : w ∈ W₂), ψ (f ∘ w) = f ∘ (e.symm ⟨w, hw⟩ : Fin a → k)`. Introduce `w hw`.

Use `show ((LinearMap.toMatrix' g₂).map f).mulVec (f ∘ w) = _`. Rewrite using `[key, LinearMap.toMatrix'_mulVec]`. Conclude with `congrArg _ (hg₂' ⟨w, hw⟩)`. Use `set S₁ := (fun v => f ∘ v) '' (W₁ : Set (Fin a → k)) with hS₁`. Use `set S₂ := (fun v => f ∘ v) '' (W₂ : Set (Fin a → k)) with hS₂`.

Establish `mφ : ∀ x ∈ Submodule.span L S₁, φ x ∈ Submodule.span L S₂`. Introduce `x hx`. Establish `: Submodule.span L S₁ ≤ (Submodule.span L S₂).comap φ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `φ (f ∘ w) ∈ Submodule.span L S₂`. Rewrite using `[hφ w hw]`. Conclude with `Submodule.subset_span ⟨_, (e ⟨w, hw⟩).2, rfl⟩`. Conclude with `this hx`.

Establish `mψ : ∀ x ∈ Submodule.span L S₂, ψ x ∈ Submodule.span L S₁`. Introduce `x hx`. Establish `: Submodule.span L S₂ ≤ (Submodule.span L S₁).comap ψ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `ψ (f ∘ w) ∈ Submodule.span L S₁`. Rewrite using `[hψ w hw]`. Conclude with `Submodule.subset_span ⟨_, (e.symm ⟨w, hw⟩).2, rfl⟩`. Conclude with `this hx`.

Establish `ψφ : ∀ x ∈ Submodule.span L S₁, ψ (φ x) = x`. Introduce `x hx`. Establish `: Set.EqOn (ψ ∘ₗ φ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₁`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply]`.

Rewrite using `[hφ w hw, hψ _ (e ⟨w, hw⟩).2]`. Simplify using the standard rewrite rules. Conclude with `LinearMap.eqOn_span' this hx`. Establish `φψ : ∀ x ∈ Submodule.span L S₂, φ (ψ x) = x`. Introduce `x hx`.

Establish `: Set.EqOn (φ ∘ₗ ψ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₂`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply]`. Rewrite using `[hψ w hw, hφ _ (e.symm ⟨w, hw⟩).2]`. Simplify using the standard rewrite rules.

Conclude with `LinearMap.eqOn_span' this hx`. Set `φ' : Submodule.span L S₁ →ₗ[L] Submodule.span L S₂` to `φ.restrict mφ`. Set `ψ' : Submodule.span L S₂ →ₗ[L] Submodule.span L S₁` to `ψ.restrict mψ`. Use `⟨LinearEquiv.ofLinear φ' ψ' (LinearMap.ext fun x => Subtype.ext (φψ x x.2)) (LinearMap.ext fun x => Subtype.ext (ψφ x x.2)), ?_⟩` and prove the remaining obligations. Introduce `g v hv`.

Use `show φ (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec v) = ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec (φ v)`. Establish `: Set.EqOn (φ ∘ₗ ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin) (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin ∘ₗ φ) S₁`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Simplify using `only [LinearMap.comp_apply, Matrix.mulVecLin_apply]`. Establish `hgw : (ρ g : Matrix (Fin a) (Fin a) k).mulVec w ∈ W₁` using `h₁ g w hw`.

Rewrite using `[key, hφ _ hgw, hφ w hw, key]`. Use `congr 1`. Conclude with `he g ⟨w, hw⟩ hgw`. Conclude with `LinearMap.eqOn_span' this v.2`.
-/
theorem isoSub_span_map : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsInv ρ W₁ → IsInv ρ W₂ → IsoSub ρ W₁ W₂ → IsoSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k)))) (Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k)))) := by
  intro k Γ _ _ L _ f a ρ W₁ W₂ h₁ h₂ ⟨e, he⟩
  obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend (W₂.subtype ∘ₗ (e : W₁ →ₗ[k] W₂))
  obtain ⟨g₂, hg₂⟩ := LinearMap.exists_extend (W₁.subtype ∘ₗ (e.symm : W₂ →ₗ[k] W₁))
  have hg₁' : ∀ v : W₁, g₁ v = (e v : Fin a → k) := fun v => by
    simpa using LinearMap.congr_fun hg₁ v
  have hg₂' : ∀ v : W₂, g₂ v = (e.symm v : Fin a → k) := fun v => by
    simpa using LinearMap.congr_fun hg₂ v
  have key : ∀ (M : Matrix (Fin a) (Fin a) k) (v : Fin a → k),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v; funext i; exact (RingHom.map_mulVec f M v i).symm
  let φ : (Fin a → L) →ₗ[L] (Fin a → L) := ((LinearMap.toMatrix' g₁).map f).mulVecLin
  let ψ : (Fin a → L) →ₗ[L] (Fin a → L) := ((LinearMap.toMatrix' g₂).map f).mulVecLin
  have hφ : ∀ w (hw : w ∈ W₁), φ (f ∘ w) = f ∘ (e ⟨w, hw⟩ : Fin a → k) := by
    intro w hw
    show ((LinearMap.toMatrix' g₁).map f).mulVec (f ∘ w) = _
    rw [key, LinearMap.toMatrix'_mulVec]
    exact congrArg _ (hg₁' ⟨w, hw⟩)
  have hψ : ∀ w (hw : w ∈ W₂), ψ (f ∘ w) = f ∘ (e.symm ⟨w, hw⟩ : Fin a → k) := by
    intro w hw
    show ((LinearMap.toMatrix' g₂).map f).mulVec (f ∘ w) = _
    rw [key, LinearMap.toMatrix'_mulVec]
    exact congrArg _ (hg₂' ⟨w, hw⟩)
  set S₁ := (fun v => f ∘ v) '' (W₁ : Set (Fin a → k)) with hS₁
  set S₂ := (fun v => f ∘ v) '' (W₂ : Set (Fin a → k)) with hS₂
  have mφ : ∀ x ∈ Submodule.span L S₁, φ x ∈ Submodule.span L S₂ := by
    intro x hx
    have : Submodule.span L S₁ ≤ (Submodule.span L S₂).comap φ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change φ (f ∘ w) ∈ Submodule.span L S₂
      rw [hφ w hw]
      exact Submodule.subset_span ⟨_, (e ⟨w, hw⟩).2, rfl⟩
    exact this hx
  have mψ : ∀ x ∈ Submodule.span L S₂, ψ x ∈ Submodule.span L S₁ := by
    intro x hx
    have : Submodule.span L S₂ ≤ (Submodule.span L S₁).comap ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change ψ (f ∘ w) ∈ Submodule.span L S₁
      rw [hψ w hw]
      exact Submodule.subset_span ⟨_, (e.symm ⟨w, hw⟩).2, rfl⟩
    exact this hx
  have ψφ : ∀ x ∈ Submodule.span L S₁, ψ (φ x) = x := by
    intro x hx
    have : Set.EqOn (ψ ∘ₗ φ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₁ := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hφ w hw, hψ _ (e ⟨w, hw⟩).2]
      simp
    exact LinearMap.eqOn_span' this hx
  have φψ : ∀ x ∈ Submodule.span L S₂, φ (ψ x) = x := by
    intro x hx
    have : Set.EqOn (φ ∘ₗ ψ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₂ := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hψ w hw, hφ _ (e.symm ⟨w, hw⟩).2]
      simp
    exact LinearMap.eqOn_span' this hx
  let φ' : Submodule.span L S₁ →ₗ[L] Submodule.span L S₂ := φ.restrict mφ
  let ψ' : Submodule.span L S₂ →ₗ[L] Submodule.span L S₁ := ψ.restrict mψ
  refine ⟨LinearEquiv.ofLinear φ' ψ'
    (LinearMap.ext fun x => Subtype.ext (φψ x x.2))
    (LinearMap.ext fun x => Subtype.ext (ψφ x x.2)), ?_⟩
  intro g v hv
  show φ (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec v)
      = ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec (φ v)
  have : Set.EqOn (φ ∘ₗ ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin)
      (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin ∘ₗ φ) S₁ := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply]
    have hgw : (ρ g : Matrix (Fin a) (Fin a) k).mulVec w ∈ W₁ := h₁ g w hw
    rw [key, hφ _ hgw, hφ w hw, key]
    congr 1
    exact he g ⟨w, hw⟩ hgw
  exact LinearMap.eqOn_span' this v.2

end GlobalTheory
