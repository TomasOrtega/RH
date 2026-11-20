import Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPfCone

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem free_mono (R : Type) [CommRing R] {A B : PSh} (g : A ⟶ B) [Mono g] : Mono ((free R).map g) := by
  have : Mono ((freeP R).map g) := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    have hg : Function.Injective (g.app U) := (mono_iff_injective _).1 (inferInstance)
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (g.app U))).hom
    have hu : Function.Injective (uliftFunctor.{1}.map (g.app U)) := by
      intro a b h
      exact ULift.ext _ _ (hg (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  change Mono ((presheafToSheaf _ _).map ((freeP R).map g))
  infer_instance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem leafChainsMono : LeafChainsMono := by
  intro R _ E' E f hf n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
    change Mono ((HomologicalComplex.extendMap ((chainsN R).map f) _).f _)
    rw [HomologicalComplex.extendMap_f _ _ h]
    have : Mono (f.app (op (SimplexCategory.mk p))) := by
      rw [NatTrans.mono_iff_mono_app] at hf
      exact hf _
    have : Mono (((chainsN R).map f).f p) := by
      change Mono ((AlgebraicTopology.AlternatingFaceMapComplex.map _).f p)
      rw [AlgebraicTopology.AlternatingFaceMapComplex.map_f]
      exact free_mono R _
    infer_instance
  · push Not at hn
    refine ⟨fun g h _ => ?_⟩
    exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)).eq_of_tgt _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etaleSplitExcision_of_cokernel_relative (hK : LeafCokIso) (hR : LeafHsRel) : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  etaleSplitExcision_of_mono_cokernel_relative leafChainsMono hK hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
