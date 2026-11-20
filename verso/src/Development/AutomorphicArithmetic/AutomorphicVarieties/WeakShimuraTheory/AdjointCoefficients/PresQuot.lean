import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `Λ R' R _ _ _ _ _ a b τ _ g e hP hg he`. Take `⟨π, f, hπ, hk⟩` from `hP`. Take `⟨σ⟩ : Nonempty (τ ≃ Fin (Nat.card τ))` from `⟨Finite.equivFin τ⟩`. Use `choose l hl using fun t => hπ (e t)`. Use `⟨g.comp π, Fin.append f (l ∘ σ.symm), hg.comp hπ, ?_⟩` and prove the remaining obligations.

Establish `hrange : Set.range (Fin.append f (l ∘ σ.symm)) = Set.range f ∪ Set.range l`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Proceed by induction on `i using Fin.addCases with`.

Consider the case `left i => exact Or.inl ⟨i, by simp⟩`. Consider the case `right i => exact Or.inr ⟨σ.symm i, by simp⟩`. Introduce and unpack `(⟨i, rfl⟩ | ⟨t, rfl⟩)`. Conclude with `⟨Fin.castAdd _ i, by simp⟩`. Conclude with `⟨Fin.natAdd _ (σ t), by simp⟩`.

Establish `hker : RingHom.ker (g.comp π) = Ideal.comap π (RingHom.ker g)`. Use extensionality with `x`. Simplify using `[RingHom.mem_ker]`. Establish `hmap : Ideal.span (Set.range e) = Ideal.map π (Ideal.span (Set.range l))`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`.

Use `congr 2`. Use function extensionality and compare the values at `t`. Conclude with `(hl t).symm`. Rewrite using `[hker, he, hmap, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hk, hrange, Ideal.span_union, sup_comm]`.
-/
theorem UpperTheory.V.Ws.X1.presQuot :
    ∀ (Λ R' R : Type) [CommRing Λ] [CommRing R'] [Algebra Λ R'] [CommRing R] [Algebra Λ R] (a b : ℕ) (τ : Type) [Finite τ] (g : R' →ₐ[Λ] R) (e : τ → R'), HasPres Λ R' a b → Function.Surjective g → RingHom.ker g = Ideal.span (Set.range e) → HasPres Λ R a (b + Nat.card τ) := by
  intro Λ R' R _ _ _ _ _ a b τ _ g e hP hg he
  obtain ⟨π, f, hπ, hk⟩ := hP
  obtain ⟨σ⟩ : Nonempty (τ ≃ Fin (Nat.card τ)) := ⟨Finite.equivFin τ⟩
  choose l hl using fun t => hπ (e t)
  refine ⟨g.comp π, Fin.append f (l ∘ σ.symm), hg.comp hπ, ?_⟩
  have hrange : Set.range (Fin.append f (l ∘ σ.symm)) = Set.range f ∪ Set.range l := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i => exact Or.inl ⟨i, by simp⟩
      | right i => exact Or.inr ⟨σ.symm i, by simp⟩
    · rintro (⟨i, rfl⟩ | ⟨t, rfl⟩)
      · exact ⟨Fin.castAdd _ i, by simp⟩
      · exact ⟨Fin.natAdd _ (σ t), by simp⟩
  have hker : RingHom.ker (g.comp π) = Ideal.comap π (RingHom.ker g) := by
    ext x
    simp [RingHom.mem_ker]
  have hmap : Ideal.span (Set.range e) = Ideal.map π (Ideal.span (Set.range l)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext t
    exact (hl t).symm
  rw [hker, he, hmap, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hk, hrange,
    Ideal.span_union, sup_comm]
