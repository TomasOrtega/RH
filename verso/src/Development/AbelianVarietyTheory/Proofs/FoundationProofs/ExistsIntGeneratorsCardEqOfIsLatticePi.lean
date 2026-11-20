import Mathlib
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E (Λ : Set (Fin n → E))`. Rewrite using `[Submodule.IsLattice.span_eq_top (self := hΛ)]`. Discharge the goal by the elementary cases of `trivial`. Establish `key : ∀ c : E, c • x ∈ S`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy`. Introduce `c`. Rewrite using `[← (integralBasis E).sum_repr c, Finset.sum_smul]`. Use `S.sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc]`.

Use `S.smul_mem _ (hS _ ?_)` and prove the remaining obligations. Rewrite using `[integralBasis_apply, algebraMap_smul]`. Conclude with `Λ.smul_mem _ hy`. Consider the case `zero => intro c`. Simplify using the standard rewrite rules.

Consider the case `add y z _ _ hy hz => intro c`. Rewrite using `[smul_add]`. Conclude with `S.add_mem (hy c) (hz c)`. Consider the case `smul a y _ hy => intro c`. Rewrite using `[smul_smul]`.

Conclude with `hy _`. Simplify using `using key 1`.
-/
theorem mem_ratSpan_of_isLattice_pi (E : Type) [Field E] [NumberField E] (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (S : Submodule ℚ (Fin n → E)) (hS : ∀ x ∈ Λ, x ∈ S) (x : Fin n → E) : x ∈ S := by
  have hx : x ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    rw [Submodule.IsLattice.span_eq_top (self := hΛ)]; trivial
  have key : ∀ c : E, c • x ∈ S := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro c
      rw [← (integralBasis E).sum_repr c, Finset.sum_smul]
      refine S.sum_mem fun i _ => ?_
      rw [smul_assoc]
      refine S.smul_mem _ (hS _ ?_)
      rw [integralBasis_apply, algebraMap_smul]
      exact Λ.smul_mem _ hy
    | zero => intro c; simp
    | add y z _ _ hy hz => intro c; rw [smul_add]; exact S.add_mem (hy c) (hz c)
    | smul a y _ hy => intro c; rw [smul_smul]; exact hy _
  simpa using key 1

/- English proof (translation)
Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hΛ))`. Establish `: Module.Finite ℤ Λ` using `Module.Finite.trans (𝓞 E) Λ`. Establish `: Module.Free ℤ Λ` using `inferInstance`. Set `b` to `Module.Free.chooseBasis ℤ Λ`. Set `f : Λ →ₗ[ℤ] (Fin n → E)` to `Λ.subtype.toAddMonoidHom.toIntLinearMap`.

Establish `hf : Function.Injective f` using `Subtype.val_injective`. Set `v : Module.Free.ChooseBasisIndex ℤ Λ → Fin n → E` to `f ∘ b`. Establish `hZ : LinearIndependent ℤ v` using `b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)`. Establish `hspan : ∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range v)`. Introduce `x`.

Establish `h` using `congrArg (Submodule.map f) b.span_eq`. Rewrite `h` using `[Submodule.map_span, ← Set.range_comp, Submodule.map_top]`. Express the relevant statement in the definitionally equal form `x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range (f ∘ b))`. Rewrite using `[h]`. Conclude with `⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩`.

Establish `hQ : Submodule.span ℚ (Set.range v) = ⊤` using `eq_top_iff.2 fun x _ => mem_ratSpan_of_isLattice_pi E n Λ hΛ _ (fun y hy => Submodule.span_le_restrictScalars ℤ ℚ _ ((hspan y).1 hy)) x`. Establish `hQi : LinearIndependent ℚ v` using `(LinearIndependent.iff_fractionRing ℤ ℚ).1 hZ`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = Module.finrank ℚ E * n`. Rewrite using `[← finrank_span_eq_card hQi, hQ, finrank_top, Module.finrank_pi_fintype]`. Simplify using `[mul_comm]`.

Set `e` to `Fintype.equivFinOfCardEq hcard`. Establish `hr : Set.range (v ∘ e.symm) = Set.range v` using `e.symm.surjective.range_comp v`. Conclude with `⟨v ∘ e.symm, by rw [hr]; exact hspan, by rw [hr]; exact hQ⟩`.
-/
theorem exists_intGenerators_card_eq_of_isLattice_pi (E : Type) [Field E] [NumberField E] (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ) :
    ∃ u : Fin (Module.finrank ℚ E * n) → Fin n → E,
      (∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range u)) ∧ Submodule.span ℚ (Set.range u) = ⊤ := by
  classical
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hΛ))
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  have : Module.Free ℤ Λ := inferInstance
  let b := Module.Free.chooseBasis ℤ Λ
  let f : Λ →ₗ[ℤ] (Fin n → E) := Λ.subtype.toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  let v : Module.Free.ChooseBasisIndex ℤ Λ → Fin n → E := f ∘ b
  have hZ : LinearIndependent ℤ v := b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
  have hspan : ∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range v) := by
    intro x
    have h := congrArg (Submodule.map f) b.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top] at h
    change x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range (f ∘ b))
    rw [h]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  have hQ : Submodule.span ℚ (Set.range v) = ⊤ :=
    eq_top_iff.2 fun x _ => mem_ratSpan_of_isLattice_pi E n Λ hΛ _
      (fun y hy => Submodule.span_le_restrictScalars ℤ ℚ _ ((hspan y).1 hy)) x
  have hQi : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hZ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = Module.finrank ℚ E * n := by
    rw [← finrank_span_eq_card hQi, hQ, finrank_top, Module.finrank_pi_fintype]
    simp [mul_comm]
  let e := Fintype.equivFinOfCardEq hcard
  have hr : Set.range (v ∘ e.symm) = Set.range v := e.symm.surjective.range_comp v
  exact ⟨v ∘ e.symm, by rw [hr]; exact hspan, by rw [hr]; exact hQ⟩

end GlobalTheory
