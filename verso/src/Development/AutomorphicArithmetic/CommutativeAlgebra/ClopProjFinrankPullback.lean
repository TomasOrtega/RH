import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFiniteEtaleOfIsClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma UpperTheory.isPullback_whisker_fst {S : Scheme.{0}} {T T' G : Over S} (y : T' ⟶ T) :
    IsPullback (y ▷ G).left (fst T' G).left (fst T G).left y.left := by
  have h : IsPullback (y ▷ G) (fst T' G) (fst T G) y := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift s.snd (s.fst ≫ snd _ _)) ?_ ?_ ?_⟩⟩
    · intro s
      apply CartesianMonoidalCategory.hom_ext
      · simp [s.condition]
      · simp
    · intro s
      simp
    · intro s m h1 h2
      apply CartesianMonoidalCategory.hom_ext
      · simpa using h2
      · simp only [lift_snd]
        rw [← h1, Category.assoc, whiskerRight_snd]
  exact h.map (Over.forget S)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.clopProj_finrank_pullback :
    ∀ {S : Scheme.{0}} {T T' G : Over S} (y : T' ⟶ T) (V : (T ⊗ G).left.Opens), IsFinite G.hom → Etale G.hom → IsClosed (V : Set (T ⊗ G).left) → ∀ t : T'.left, (UpperTheory.RepresentationRank.proj ((y ▷ G).left ⁻¹ᵁ V)).finrank t = (UpperTheory.RepresentationRank.proj V).finrank (y.left t) := by
  intro S T T' G y V hfin het hcl t
  obtain ⟨hF, hE⟩ := UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hcl
  have hsq := (isPullback_morphismRestrict (y ▷ G).left V).paste_vert (UpperTheory.isPullback_whisker_fst y)
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq t
