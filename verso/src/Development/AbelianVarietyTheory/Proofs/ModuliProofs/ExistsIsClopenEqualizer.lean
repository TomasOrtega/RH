import Mathlib

open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.ClopenEqualizer

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_isClopen_equalizer {P C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (a b : P ⟶ C)
    (h : a ≫ c = b ≫ c) :
    ∃ (U : Set P), IsClopen U ∧ ∀ (T : Scheme.{0}) (y : T ⟶ P), y ≫ a = y ≫ b ↔ Set.range y ⊆ U := by
  let d := pullback.diagonal c
  let l : P ⟶ pullback c c := pullback.lift a b h
  haveI : IsOpenImmersion d := inferInstance
  haveI : IsClosedImmersion d := inferInstance
  let j : pullback l d ⟶ P := pullback.fst l d
  have hj : j ≫ a = j ≫ b := by
    have h0 : j ≫ l = pullback.snd l d ≫ d := pullback.condition
    have h1 := congrArg (· ≫ pullback.fst c c) h0
    have h2 := congrArg (· ≫ pullback.snd c c) h0
    simp [l, d, pullback.lift_fst, pullback.lift_snd] at h1 h2
    rw [h1, h2]
  refine ⟨Set.range j, ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩, ?_⟩
  intro T y
  constructor
  · intro hy
    have e : y ≫ l = (y ≫ a) ≫ d := by
      apply pullback.hom_ext
      · simp [l, d, pullback.lift_fst]
      · simp [l, d, hy, pullback.lift_snd]
    have e2 : pullback.lift y (y ≫ a) e ≫ j = y := pullback.lift_fst _ _ _
    rintro _ ⟨t, rfl⟩
    refine ⟨pullback.lift y (y ≫ a) e t, ?_⟩
    rw [← Scheme.Hom.comp_apply, e2]
  · intro hy
    rw [← IsOpenImmersion.lift_fac j y hy, Category.assoc, Category.assoc, hj]

end GlobalTheory.ClopenEqualizer
