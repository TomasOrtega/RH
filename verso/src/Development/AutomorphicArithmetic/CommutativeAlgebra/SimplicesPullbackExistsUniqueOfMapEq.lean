import Development.AutomorphicArithmetic.BlowupCategories.SpanScale

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
