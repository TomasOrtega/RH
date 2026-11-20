import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ L _ f a W₁ W₂ h`. Establish `hker : LinearMap.ker (W₂.mkQ ∘ₗ W₁.subtype) = ⊥`. Use `LinearMap.ker_eq_bot'.mpr ?_` and prove the remaining obligations. Introduce `w hw`. Establish `hw2 : (w : Fin a → k) ∈ W₂`.

Simplify `hw` using `[Submodule.Quotient.mk_eq_zero]`. Establish `hw12 : (w : Fin a → k) ∈ W₁ ⊓ W₂` using `⟨w.2, hw2⟩`. Rewrite `hw12` using `[h]`. Conclude with `Subtype.ext (by simpa using hw12)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hker`.

Set `p : (Fin a → k) →ₗ[k] (Fin a → k)` to `W₁.subtype ∘ₗ g ∘ₗ W₂.mkQ`. Establish `hp1 : ∀ w ∈ W₁, p w = w`. Introduce `w hw`. Use `LinearMap.congr_fun hg (⟨w, hw⟩ : W₁)` as an intermediate fact. Establish `h2 : g (W₂.mkQ w) = ⟨w, hw⟩` using `by simpa using this`.

Simplify using `only [p, LinearMap.comp_apply, h2]`. Both sides reduce to the same expression. Establish `hp2 : ∀ w ∈ W₂, p w = 0`. Introduce `w hw`. Establish `h2 : W₂.mkQ w = 0` using `by simpa [Submodule.Quotient.mk_eq_zero] using hw`.

Simplify using `[p, h2]`. Set `P : (Fin a → L) →ₗ[L] (Fin a → L)` to `Matrix.mulVecLin ((LinearMap.toMatrix' p).map f)`. Establish `hP : ∀ v : Fin a → k, P (f ∘ v) = f ∘ (p v)`. Introduce `v`. Use function extensionality and compare the values at `i`.

Use `RingHom.map_mulVec f (LinearMap.toMatrix' p) v i` as an intermediate fact. Simplify `this.symm` using `[P, LinearMap.toMatrix'_mulVec]`. Establish `hS1 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))), P x = x`. Introduce `x hx`. Establish `heq : Set.EqOn P (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k)))`.

Introduce and unpack `_ ⟨v, hv, rfl⟩`. Simplify using `only [LinearMap.id_apply]`. Rewrite using `[hP, hp1 v hv]`. Conclude with `LinearMap.eqOn_span heq hx`. Establish `hS2 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))), P x = 0`.

Introduce `x hx`. Establish `heq : Set.EqOn P (0 : (Fin a → L) →ₗ[L] (Fin a → L)) ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k)))`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Simplify using `only [LinearMap.zero_apply]`. Rewrite using `[hP, hp2 v hv]`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Conclude with `LinearMap.eqOn_span heq hx`. Use `(Submodule.eq_bot_iff _).mpr ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hx1, hx2⟩`.

Rewrite using `[← hS1 x hx1, hS2 x hx2]`.
-/
theorem span_map_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L)
    {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ →
    Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓
      Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  intro k _ L _ f a W₁ W₂ h
  have hker : LinearMap.ker (W₂.mkQ ∘ₗ W₁.subtype) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro w hw
    have hw2 : (w : Fin a → k) ∈ W₂ := by
      simpa [Submodule.Quotient.mk_eq_zero] using hw
    have hw12 : (w : Fin a → k) ∈ W₁ ⊓ W₂ := ⟨w.2, hw2⟩
    rw [h] at hw12
    exact Subtype.ext (by simpa using hw12)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  let p : (Fin a → k) →ₗ[k] (Fin a → k) := W₁.subtype ∘ₗ g ∘ₗ W₂.mkQ
  have hp1 : ∀ w ∈ W₁, p w = w := by
    intro w hw
    have := LinearMap.congr_fun hg (⟨w, hw⟩ : W₁)
    have h2 : g (W₂.mkQ w) = ⟨w, hw⟩ := by simpa using this
    simp only [p, LinearMap.comp_apply, h2]
    rfl
  have hp2 : ∀ w ∈ W₂, p w = 0 := by
    intro w hw
    have h2 : W₂.mkQ w = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using hw
    simp [p, h2]
  let P : (Fin a → L) →ₗ[L] (Fin a → L) := Matrix.mulVecLin ((LinearMap.toMatrix' p).map f)
  have hP : ∀ v : Fin a → k, P (f ∘ v) = f ∘ (p v) := by
    intro v
    funext i
    have := RingHom.map_mulVec f (LinearMap.toMatrix' p) v i
    simpa [P, LinearMap.toMatrix'_mulVec] using this.symm
  have hS1 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))), P x = x := by
    intro x hx
    have heq : Set.EqOn P (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L))
        ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) := by
      rintro _ ⟨v, hv, rfl⟩
      simp only [LinearMap.id_apply]
      rw [hP, hp1 v hv]
    exact LinearMap.eqOn_span heq hx
  have hS2 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))), P x = 0 := by
    intro x hx
    have heq : Set.EqOn P (0 : (Fin a → L) →ₗ[L] (Fin a → L))
        ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) := by
      rintro _ ⟨v, hv, rfl⟩
      simp only [LinearMap.zero_apply]
      rw [hP, hp2 v hv]
      funext i
      simp
    exact LinearMap.eqOn_span heq hx
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro x ⟨hx1, hx2⟩
  rw [← hS1 x hx1, hS2 x hx2]

end GlobalTheory
