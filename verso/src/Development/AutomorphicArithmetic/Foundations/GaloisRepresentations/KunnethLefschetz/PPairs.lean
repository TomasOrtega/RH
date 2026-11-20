import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Unfold `Pairs`. Introduce `k _ d X p hsep hsm`. Establish `hfst : SmoothOfRelativeDimension d (pullback.fst p p)` using `(smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback (IsPullback.of_hasPullback p p).flip hsm`. Establish `hcomp : SmoothOfRelativeDimension (d + d) (pullback.fst p p ≫ p)` using `smoothOfRelativeDimension_comp (n := d) (m := d) (pullback.fst p p) p`. Establish `hid : SmoothOfRelativeDimension 0 (𝟙 (S k))` using `inferInstance`.

Use `⟨⟨inferInstance, hcomp, ?_⟩, fun y => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[pullback.diagonal_fst_assoc]`. Conclude with `hsm`. Establish `h1 : IsClosedImmersion (y.1 ≫ p)` using `by rw [y.2]; infer_instance`. Conclude with `IsClosedImmersion.of_comp y.1 p`.

Rewrite using `[Nat.zero_add]`. Conclude with `hsm`. Rewrite using `[y.2]`. Conclude with `hid`. Establish `key : ∀ s : PullbackCone (slice y) (pullback.diagonal p), s.fst = s.snd ∧ s.fst ≫ p ≫ y.1 = s.snd`.

Introduce `s`. Establish `c` using `s.condition`. Establish `c1` using `congrArg (· ≫ pullback.fst p p) c`. Establish `c2` using `congrArg (· ≫ pullback.snd p p) c`. Simplify using `only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at c1 c2`.

Conclude with `⟨c1, c2⟩`. Use `IsPullback.of_isLimit' ⟨?_⟩ (PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ p) ?_ ?_ ?_)` and prove the remaining obligations. Establish `e1 : slice y ≫ pullback.fst p p = 𝟙 X` using `pullback.lift_fst _ _ _`. Establish `e2 : slice y ≫ pullback.snd p p = p ≫ y.1` using `pullback.lift_snd _ _ _`. Establish `hy : y.1 ≫ p ≫ y.1 = y.1` using `by rw [← Category.assoc, y.2, Category.id_comp]`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]`. Rewrite using `[Category.assoc, e2, hy, Category.assoc, pullback.diagonal_snd, Category.comp_id]`. Introduce `s`. Rewrite using `[Category.assoc, (key s).2, (key s).1]`.

Introduce `s`. Rewrite using `[Category.assoc, (key s).2]`. Introduce `s m h1 _`. Rewrite using `[← h1, Category.assoc, y.2, Category.comp_id]`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.pairs_holds :
    UpperTheory.Gal.KunnethLefschetz.Pairs := by
  unfold Pairs
  intro k _ d X p hsep hsm
  have hfst : SmoothOfRelativeDimension d (pullback.fst p p) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (IsPullback.of_hasPullback p p).flip hsm
  have hcomp : SmoothOfRelativeDimension (d + d) (pullback.fst p p ≫ p) :=
    smoothOfRelativeDimension_comp (n := d) (m := d) (pullback.fst p p) p
  have hid : SmoothOfRelativeDimension 0 (𝟙 (S k)) := inferInstance
  refine ⟨⟨inferInstance, hcomp, ?_⟩, fun y => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · rw [pullback.diagonal_fst_assoc]
    exact hsm
  · have h1 : IsClosedImmersion (y.1 ≫ p) := by rw [y.2]; infer_instance
    exact IsClosedImmersion.of_comp y.1 p
  · rw [Nat.zero_add]; exact hsm
  · rw [y.2]; exact hid
  · have key : ∀ s : PullbackCone (slice y) (pullback.diagonal p),
        s.fst = s.snd ∧ s.fst ≫ p ≫ y.1 = s.snd := by
      intro s
      have c := s.condition
      have c1 := congrArg (· ≫ pullback.fst p p) c
      have c2 := congrArg (· ≫ pullback.snd p p) c
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
        pullback.diagonal_snd, Category.comp_id] at c1 c2
      exact ⟨c1, c2⟩
    refine IsPullback.of_isLimit' ⟨?_⟩ (PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ p) ?_ ?_ ?_)
    · have e1 : slice y ≫ pullback.fst p p = 𝟙 X := pullback.lift_fst _ _ _
      have e2 : slice y ≫ pullback.snd p p = p ≫ y.1 := pullback.lift_snd _ _ _
      have hy : y.1 ≫ p ≫ y.1 = y.1 := by rw [← Category.assoc, y.2, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, e2, hy, Category.assoc, pullback.diagonal_snd, Category.comp_id]
    · intro s
      rw [Category.assoc, (key s).2, (key s).1]
    · intro s
      rw [Category.assoc, (key s).2]
    · intro s m h1 _
      rw [← h1, Category.assoc, y.2, Category.comp_id]
