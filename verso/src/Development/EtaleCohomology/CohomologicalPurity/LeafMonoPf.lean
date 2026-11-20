import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions.

A detailed English derivation is pending.
-/
theorem mono_freeP (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) [Mono g] : Mono ((freeP R).map g) := by
  have : ∀ U, Mono (((freeP R).map g).app U) := by
    intro U
    have hg : Function.Injective (g.app U) := (mono_iff_injective _).1 inferInstance
    rw [ModuleCat.mono_iff_injective]
    dsimp [freeP]
    exact Finsupp.mapDomain_injective (fun a b h => ULift.ext _ _ (hg (congrArg ULift.down h)))
  exact NatTrans.mono_of_mono_app _

/- English proof (translation)
Establish an intermediate fact. Simplify by unfolding definitions. A detailed English derivation is pending.
-/
theorem mono_free (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) [Mono g] : Mono ((free R).map g) := by
  have := mono_freeP R g
  dsimp [free]
  infer_instance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem LeafMono_of : LeafMono := by
  intro R _ U E f hf p
  have hk : ∀ k : ℕ, Mono (((chainsN R).map f).f k) := by
    intro k
    have : Mono (f.app (op (SimplexCategory.mk k))) := inferInstance
    have := mono_free R (f.app (op (SimplexCategory.mk k)))
    simp only [chainsN, Functor.comp_map, AlgebraicTopology.alternatingFaceMapComplex_map_f]
    exact this
  by_cases h : ∃ k : ℕ, -(k : ℤ) = p
  · obtain ⟨k, rfl⟩ := h
    have e := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := k) (i' := -(k:ℤ)) rfl
    change Mono (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f _)
    rw [e]
    have := hk k
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) := by
      apply HomologicalComplex.isZero_extend_X
      intro k hk; exact h ⟨k, hk⟩
    exact hz.mono _
