import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
open scoped TensorProduct

namespace GlobalTheory.OuterTensor

/- English proof (translation)
Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Establish `hne : (⊥ : Subrepresentation ρ) ≠ ⊤` using `bot_ne_top`. Conclude with `hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))`.
-/
theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  exact hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

/- English proof (translation)
Introduce `G H V W _ _ _ _ _ _ _ _ ρ σ hρ hσ`. Establish `hV` using `nontrivial_of_isIrreducible ρ hρ`. Establish `hW` using `nontrivial_of_isIrreducible σ hσ`. Establish `sρ` using `GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible G V ρ hρ`. Establish `sσ` using `GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hσ`.

Establish `hVW : Nontrivial (V ⊗[ℂ] W)`. Apply `Module.nontrivial_of_finrank_pos (R := ℂ)` to reduce the goal to its premises. Rewrite using `[Module.finrank_tensorProduct]`. Conclude with `Nat.mul_pos Module.finrank_pos Module.finrank_pos`. Use `{ exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }` and prove the remaining obligations.

Conclude with `bot_ne_top (congrArg Subrepresentation.toSubmodule h : (⊥ : Submodule ℂ (V ⊗[ℂ] W)) = ⊤)`. Establish `h1 : ∀ (g : G) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule, TensorProduct.map (ρ g) B x ∈ S.toSubmodule`. Introduce `g B`. Establish `hB : B ∈ Submodule.span ℂ (Set.range σ)` using `sσ ▸ Submodule.mem_top`. Proceed by induction on `hB using Submodule.span_induction with`.

Consider the case `mem B hB`. Take `⟨h, rfl⟩` from `hB`. Introduce `x hx`. Conclude with `S.apply_mem_toSubmodule (g, h) hx`. Consider the case `zero => intro x _`.

Simplify using the standard rewrite rules. Consider the case `add B C _ _ hB hC`. Introduce `x hx`. Rewrite using `[TensorProduct.map_add_right, LinearMap.add_apply]`. Conclude with `add_mem (hB x hx) (hC x hx)`.

Consider the case `smul c B _ hB`. Introduce `x hx`. Rewrite using `[TensorProduct.map_smul_right, LinearMap.smul_apply]`. Conclude with `Submodule.smul_mem _ _ (hB x hx)`. Establish `h2 : ∀ (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule, TensorProduct.map A B x ∈ S.toSubmodule`.

Introduce `A B`. Establish `hA : A ∈ Submodule.span ℂ (Set.range ρ)` using `sρ ▸ Submodule.mem_top`. Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A hA`. Take `⟨g, rfl⟩` from `hA`.

Conclude with `h1 g B`. Consider the case `zero => intro x _`. Simplify using the standard rewrite rules. Consider the case `add A C _ _ hA hC`. Introduce `x hx`.

Rewrite using `[TensorProduct.map_add_left, LinearMap.add_apply]`. Conclude with `add_mem (hA x hx) (hC x hx)`. Consider the case `smul c A _ hA`. Introduce `x hx`. Rewrite using `[TensorProduct.map_smul_left, LinearMap.smul_apply]`.

Conclude with `Submodule.smul_mem _ _ (hA x hx)`. Establish `h3 : ∀ (F : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W), ∀ x ∈ S.toSubmodule, F x ∈ S.toSubmodule`. Introduce `F`. Take `⟨t, rfl⟩` from `(homTensorHomEquiv ℂ V W V W).surjective F`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => intro x _`. Simplify using the standard rewrite rules. Consider the case `tmul A B`. Introduce `x hx`. Rewrite using `[homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]`.

Conclude with `h2 A B x hx`. Consider the case `add s t hs ht`. Introduce `x hx`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `add_mem (hs x hx) (ht x hx)`.

Distinguish the cases in `hS : S.toSubmodule = ⊥`. Conclude with `Or.inl (Subrepresentation.toSubmodule_injective hS)`. Use `right`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hS`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `S.toSubmodule = ⊤`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_eq_one ℂ hx0`. Use `h3 (f.smulRight y) x hx` as an intermediate fact. Simplify `this` using `[hf]`.
-/
theorem isIrreducible_outer_tprod :
    ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W), ρ.IsIrreducible → σ.IsIrreducible → (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IsIrreducible := by
  intro G H V W _ _ _ _ _ _ _ _ ρ σ hρ hσ
  have hV := nontrivial_of_isIrreducible ρ hρ
  have hW := nontrivial_of_isIrreducible σ hσ
  have sρ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible G V ρ hρ
  have sσ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hσ
  have hVW : Nontrivial (V ⊗[ℂ] W) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h : (⊥ : Submodule ℂ (V ⊗[ℂ] W)) = ⊤)
  have h1 : ∀ (g : G) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map (ρ g) B x ∈ S.toSubmodule := by
    intro g B
    have hB : B ∈ Submodule.span ℂ (Set.range σ) := sσ ▸ Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨h, rfl⟩ := hB
      intro x hx
      exact S.apply_mem_toSubmodule (g, h) hx
    | zero => intro x _; simp
    | add B C _ _ hB hC =>
      intro x hx
      rw [TensorProduct.map_add_right, LinearMap.add_apply]
      exact add_mem (hB x hx) (hC x hx)
    | smul c B _ hB =>
      intro x hx
      rw [TensorProduct.map_smul_right, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hB x hx)
  have h2 : ∀ (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map A B x ∈ S.toSubmodule := by
    intro A B
    have hA : A ∈ Submodule.span ℂ (Set.range ρ) := sρ ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨g, rfl⟩ := hA
      exact h1 g B
    | zero => intro x _; simp
    | add A C _ _ hA hC =>
      intro x hx
      rw [TensorProduct.map_add_left, LinearMap.add_apply]
      exact add_mem (hA x hx) (hC x hx)
    | smul c A _ hA =>
      intro x hx
      rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hA x hx)
  have h3 : ∀ (F : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W), ∀ x ∈ S.toSubmodule, F x ∈ S.toSubmodule := by
    intro F
    obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ V W V W).surjective F
    induction t using TensorProduct.induction_on with
    | zero => intro x _; simp
    | tmul A B =>
      intro x hx
      rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
      exact h2 A B x hx
    | add s t hs ht =>
      intro x hx
      rw [map_add, LinearMap.add_apply]
      exact add_mem (hs x hx) (ht x hx)
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hx0
    have := h3 (f.smulRight y) x hx
    simpa [hf] using this

end GlobalTheory.OuterTensor
