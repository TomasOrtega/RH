import Mathlib

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
