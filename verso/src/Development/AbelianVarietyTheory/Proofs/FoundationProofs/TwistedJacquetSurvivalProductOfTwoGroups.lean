import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

/- English proof (translation)
Introduce `G₁ G₂ V _ _ _ _ _ _ _ _ ρ hρ U₁ U₂ J₁ J₂ θ₁ θ₂ h₁ h₂ v hv e₁ e₂`. Establish `s₁ : IsSmooth (ρ.comp (MonoidHom.inl G₁ G₂))` using `fun w => (hρ w).preimage (f := fun g : G₁ => ((g, 1) : G₁ × G₂)) (by fun_prop)`. Establish `s₂ : IsSmooth (ρ.comp (MonoidHom.inr G₁ G₂))` using `fun w => (hρ w).preimage (f := fun g : G₂ => ((1, g) : G₁ × G₂)) (by fun_prop)`. Use `set ρ₁ : Representation ℂ G₁ V := ρ.comp (MonoidHom.inl G₁ G₂) with hρ₁`. Use `set ρ₂ : Representation ℂ G₂ V := ρ.comp (MonoidHom.inr G₁ G₂) with hρ₂`.

Establish `comm : ∀ (a : G₁) (b : G₂) (w : V), ρ₁ a (ρ₂ b w) = ρ₂ b (ρ₁ a w)`. Introduce `a b w`. Express the relevant statement in the definitionally equal form `ρ (a, 1) (ρ (1, b) w) = ρ (1, b) (ρ (a, 1) w)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules.

Use `set A : Submodule ℂ V := twKer ρ₂ U₂ 1 with hA`. Establish `hst : ∀ g : G₁, A ≤ A.comap (ρ₁ g)`. Introduce `g`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨n, x, rfl⟩`.

Use `Submodule.subset_span ⟨n, ρ₁ g x, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, comm]`. Set `σ : Representation ℂ G₁ (V ⧸ A)` to `Representation.quotient ρ₁ A hst`. Establish `hσ : ∀ g x, σ g (A.mkQ x) = A.mkQ (ρ₁ g x)` using `fun g x => rfl`. Establish `sσ : IsSmooth σ`.

Introduce `w`. Take `⟨x, rfl⟩` from `A.mkQ_surjective w`. Set `S : Subgroup G₁` to `{ carrier := {g | σ g (A.mkQ x) = A.mkQ x} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`.

Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`.

Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`. Establish `: (S : Set G₁) ∈ nhds (1 : G₁)`. Use `Filter.mem_of_superset ((s₁ x).mem_nhds (by simp)) ?_` and prove the remaining obligations.

Introduce `g hg`. Express the relevant statement in the definitionally equal form `σ g (A.mkQ x) = A.mkQ x`. Rewrite using `[hσ, show ρ₁ g x = x from hg]`. Conclude with `S.isOpen_of_mem_nhds this`. Establish `hmap : twKer ρ₁ U₁ 1 ≤ (twKer σ U₁ 1).comap A.mkQ`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨n, x, rfl⟩`. Use `Submodule.subset_span ⟨n, A.mkQ x, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, hσ]`. Establish `hA0 : A ≤ (twKer σ U₁ 1).comap A.mkQ`.

Introduce `x hx`. Establish `: A.mkQ x = 0` using `(Submodule.Quotient.mk_eq_zero A).2 hx`. Rewrite using `[Submodule.mem_comap, this]`. Conclude with `zero_mem _`. Establish `hv' : A.mkQ v ∈ twKer σ U₁ 1` using `sup_le hmap hA0 hv`.

Establish `hz : A.mkQ v = 0` using `h₁ _ σ sσ _ hv' (by`. Introduce `h hh`. Rewrite using `[hσ, e₁ h hh, map_smul])`. Conclude with `h₂ V ρ₂ s₂ v ((Submodule.Quotient.mk_eq_zero A).1 hz) e₂`.
-/
theorem eq_zero_of_mem_sup_twKer_prod : ∀ (G₁ G₂ V : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V), IsSmooth ρ → ∀ (U₁ : Subgroup G₁) (U₂ : Subgroup G₂) (J₁ : Set G₁) (J₂ : Set G₂) (θ₁ : G₁ → ℂ) (θ₂ : G₂ → ℂ), (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₁ W), IsSmooth σ → ∀ w ∈ twKer σ U₁ 1, IsEig σ J₁ θ₁ w → w = 0) → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₂ W), IsSmooth σ → ∀ w ∈ twKer σ U₂ 1, IsEig σ J₂ θ₂ w → w = 0) → ∀ v ∈ twKer (ρ.comp (MonoidHom.inl G₁ G₂)) U₁ 1 ⊔ twKer (ρ.comp (MonoidHom.inr G₁ G₂)) U₂ 1, IsEig (ρ.comp (MonoidHom.inl G₁ G₂)) J₁ θ₁ v → IsEig (ρ.comp (MonoidHom.inr G₁ G₂)) J₂ θ₂ v → v = 0 := by
  intro G₁ G₂ V _ _ _ _ _ _ _ _ ρ hρ U₁ U₂ J₁ J₂ θ₁ θ₂ h₁ h₂ v hv e₁ e₂
  have s₁ : IsSmooth (ρ.comp (MonoidHom.inl G₁ G₂)) := fun w =>
    (hρ w).preimage (f := fun g : G₁ => ((g, 1) : G₁ × G₂)) (by fun_prop)
  have s₂ : IsSmooth (ρ.comp (MonoidHom.inr G₁ G₂)) := fun w =>
    (hρ w).preimage (f := fun g : G₂ => ((1, g) : G₁ × G₂)) (by fun_prop)
  set ρ₁ : Representation ℂ G₁ V := ρ.comp (MonoidHom.inl G₁ G₂) with hρ₁
  set ρ₂ : Representation ℂ G₂ V := ρ.comp (MonoidHom.inr G₁ G₂) with hρ₂
  have comm : ∀ (a : G₁) (b : G₂) (w : V), ρ₁ a (ρ₂ b w) = ρ₂ b (ρ₁ a w) := by
    intro a b w
    change ρ (a, 1) (ρ (1, b) w) = ρ (1, b) (ρ (a, 1) w)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp
  set A : Submodule ℂ V := twKer ρ₂ U₂ 1 with hA
  have hst : ∀ g : G₁, A ≤ A.comap (ρ₁ g) := by
    intro g
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, x, rfl⟩
    refine Submodule.subset_span ⟨n, ρ₁ g x, ?_⟩
    rw [map_sub, map_smul, comm]
  let σ : Representation ℂ G₁ (V ⧸ A) := Representation.quotient ρ₁ A hst
  have hσ : ∀ g x, σ g (A.mkQ x) = A.mkQ (ρ₁ g x) := fun g x => rfl
  have sσ : IsSmooth σ := by
    intro w
    obtain ⟨x, rfl⟩ := A.mkQ_surjective w
    let S : Subgroup G₁ :=
      { carrier := {g | σ g (A.mkQ x) = A.mkQ x}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have : (S : Set G₁) ∈ nhds (1 : G₁) := by
      refine Filter.mem_of_superset ((s₁ x).mem_nhds (by simp)) ?_
      intro g hg
      change σ g (A.mkQ x) = A.mkQ x
      rw [hσ, show ρ₁ g x = x from hg]
    exact S.isOpen_of_mem_nhds this
  have hmap : twKer ρ₁ U₁ 1 ≤ (twKer σ U₁ 1).comap A.mkQ := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, x, rfl⟩
    refine Submodule.subset_span ⟨n, A.mkQ x, ?_⟩
    rw [map_sub, map_smul, hσ]
  have hA0 : A ≤ (twKer σ U₁ 1).comap A.mkQ := by
    intro x hx
    have : A.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero A).2 hx
    rw [Submodule.mem_comap, this]
    exact zero_mem _
  have hv' : A.mkQ v ∈ twKer σ U₁ 1 := sup_le hmap hA0 hv
  have hz : A.mkQ v = 0 := h₁ _ σ sσ _ hv' (by
    intro h hh
    rw [hσ, e₁ h hh, map_smul])
  exact h₂ V ρ₂ s₂ v ((Submodule.Quotient.mk_eq_zero A).1 hz) e₂

end GlobalTheory.PsType
