import Development.AutomorphicArithmetic.BlowupCategories.SpanScale

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

/- English proof (translation)
Introduce `A B C r u k T x y h`. Set `F : Spc ⥤ Type` to `(evaluation _ _).obj (op (SimplexCategory.mk k)) ⋙ (evaluation _ _).obj (op T)`. Establish `hc` using `isLimitOfHasPullbackOfPreservesLimit F r u`. Set `e : Sx (pullback r u) k T ≃ Types.PullbackObj (F.map r) (F.map u)` to `PullbackCone.IsLimit.equivPullbackObj hc`. Establish `e1 : ∀ z : Sx (pullback r u) k T, (e z).1.1 = z.map (pullback.fst r u)` using `fun z => PullbackCone.IsLimit.equivPullbackObj_apply_fst hc z`.

Establish `e2 : ∀ z : Sx (pullback r u) k T, (e z).1.2 = z.map (pullback.snd r u)` using `fun z => PullbackCone.IsLimit.equivPullbackObj_apply_snd hc z`. Establish `key : ∀ z : Sx (pullback r u) k T, z.map (pullback.fst r u) = x ∧ z.map (pullback.snd r u) = y ↔ e z = ⟨(x, y), h⟩`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Conclude with `(e1 z).trans h1`. Conclude with `(e2 z).trans h2`. Introduce `hz`.

Use `⟨(e1 z).symm.trans ?_, (e2 z).symm.trans ?_⟩` and prove the remaining obligations. Rewrite using `[hz]`. Rewrite using `[hz]`. Use `⟨e.symm ⟨(x, y), h⟩, (key _).2 (e.apply_symm_apply _), ?_⟩` and prove the remaining obligations. Introduce `z hz`.

Rewrite using `[← (key z).1 hz, e.symm_apply_apply]`.
-/
theorem UpperTheory.simplices_pullback_existsUnique_of_map_eq :
    ∀ {A B C : Spc} (r : A ⟶ C) (u : B ⟶ C) (k : ℕ) (T : Scheme.{0}) (x : Sx A k T) (y : Sx B k T), x.map r = y.map u →
        ∃! z : Sx (pullback r u) k T, z.map (pullback.fst r u) = x ∧ z.map (pullback.snd r u) = y := by
  intro A B C r u k T x y h
  let F : Spc ⥤ Type := (evaluation _ _).obj (op (SimplexCategory.mk k)) ⋙ (evaluation _ _).obj (op T)
  have hc := isLimitOfHasPullbackOfPreservesLimit F r u
  let e : Sx (pullback r u) k T ≃ Types.PullbackObj (F.map r) (F.map u) :=
    PullbackCone.IsLimit.equivPullbackObj hc
  have e1 : ∀ z : Sx (pullback r u) k T, (e z).1.1 = z.map (pullback.fst r u) := fun z =>
    PullbackCone.IsLimit.equivPullbackObj_apply_fst hc z
  have e2 : ∀ z : Sx (pullback r u) k T, (e z).1.2 = z.map (pullback.snd r u) := fun z =>
    PullbackCone.IsLimit.equivPullbackObj_apply_snd hc z
  have key : ∀ z : Sx (pullback r u) k T,
      z.map (pullback.fst r u) = x ∧ z.map (pullback.snd r u) = y ↔ e z = ⟨(x, y), h⟩ := by
    intro z
    constructor
    · rintro ⟨h1, h2⟩
      apply Subtype.ext
      apply Prod.ext
      · exact (e1 z).trans h1
      · exact (e2 z).trans h2
    · intro hz
      refine ⟨(e1 z).symm.trans ?_, (e2 z).symm.trans ?_⟩
      · rw [hz]
      · rw [hz]
  refine ⟨e.symm ⟨(x, y), h⟩, (key _).2 (e.apply_symm_apply _), ?_⟩
  intro z hz
  rw [← (key z).1 hz, e.symm_apply_apply]
