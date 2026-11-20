import Development.EtaleCohomology.EtaleTrace.FibrePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Establish `key : ∀ {T : Scheme.{0}} (a : T ⟶ X) (b : T ⟶ S k), a ≫ π = b ≫ t.1 → a ≫ p = b`. Introduce `T a b h`. Rewrite using `[← hπ, ← Category.assoc, h, Category.assoc, t.2, Category.comp_id]`. Use `IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc]`.

Conclude with `equalizer.condition _ _`. Introduce `s`. Conclude with `equalizer.lift s.fst (by rw [s.condition, ← Category.assoc, key s.fst s.snd s.condition])`. Introduce `s`. Conclude with `equalizer.lift_ι _ _`.

Introduce `s`. Rewrite using `[← Category.assoc, equalizer.lift_ι]`. Conclude with `key s.fst s.snd s.condition`. Introduce `s m h1 _`. Apply `equalizer.hom_ext` to reduce the goal to its premises.

Conclude with `h1.trans (equalizer.lift_ι _ _).symm`.
-/
lemma isPullback_equalizer {k : Type} [Field k] {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P)
    (hπ : π ≫ r = p) (t : Pt r) :
    IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π t.1 := by
  have key : ∀ {T : Scheme.{0}} (a : T ⟶ X) (b : T ⟶ S k), a ≫ π = b ≫ t.1 → a ≫ p = b := by
    intro T a b h
    rw [← hπ, ← Category.assoc, h, Category.assoc, t.2, Category.comp_id]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_)
  · rw [Category.assoc]; exact equalizer.condition _ _
  · intro s
    exact equalizer.lift s.fst (by rw [s.condition, ← Category.assoc, key s.fst s.snd s.condition])
  · intro s; exact equalizer.lift_ι _ _
  · intro s
    rw [← Category.assoc, equalizer.lift_ι]; exact key s.fst s.snd s.condition
  · intro s m h1 _
    apply equalizer.hom_ext
    exact h1.trans (equalizer.lift_ι _ _).symm

/- English proof (translation)
Introduce `k _ X P p r π hπ V hE t ht`. Establish `hr : Set.range t.1.base ⊆ Set.range V.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `ht x`.

Use `set t' := IsOpenImmersion.lift V.ι t.1 hr`. Establish `ht' : t' ≫ V.ι = t.1` using `IsOpenImmersion.lift_fac _ _ _`. Establish `s` using `(congrArg (IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π) ht').mpr (isPullback_equalizer p r π hπ t)`. Establish `h` using `IsPullback.of_right' s (isPullback_morphismRestrict π V).flip`. Conclude with `MorphismProperty.of_isPullback h hE`.
-/
theorem FibreOfEtale_of : FibreOfEtale := by
  intro k _ X P p r π hπ V hE t ht
  have hr : Set.range t.1.base ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨x, rfl⟩; exact ht x
  set t' := IsOpenImmersion.lift V.ι t.1 hr
  have ht' : t' ≫ V.ι = t.1 := IsOpenImmersion.lift_fac _ _ _
  have s := (congrArg (IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π) ht').mpr
    (isPullback_equalizer p r π hπ t)
  have h := IsPullback.of_right' s (isPullback_morphismRestrict π V).flip
  exact MorphismProperty.of_isPullback h hE

end LateralTheory.EtaleTrace.Cov
