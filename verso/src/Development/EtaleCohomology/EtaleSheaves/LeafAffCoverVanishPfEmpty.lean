import Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme (R : Type) [CommRing R] (E : Scheme.{0}) [IsEmpty E] :
    IsZero ((free R).obj (yoneda.obj E)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _ |>.injective
  ext T : 2
  by_cases hT : IsEmpty T.unop
  · haveI := hT
    exact ((Sheaf.isTerminalOfBotCover _ T.unop
      (AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology T.unop)).isZero).eq_of_tgt _ _
  · rw [not_isEmpty_iff] at hT
    obtain ⟨t⟩ := hT
    have hP : IsEmpty ((yoneda.obj E).obj T) := ⟨fun f => isEmptyElim (f.base t)⟩
    apply IsZero.eq_of_src
    change IsZero ((ModuleCat.free (ULift.{1} R)).obj (ULift.{1} ((yoneda.obj E).obj T)))
    rw [ModuleCat.isZero_iff_subsingleton]
    haveI : IsEmpty (ULift.{1} ((yoneda.obj E).obj T)) := inferInstance
    change Subsingleton (ULift.{1} ((yoneda.obj E).obj T) →₀ ULift.{1} R)
    infer_instance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem leafEmptyVanish : LeafEmptyVanish := by
  intro R _ X F n
  have hE : IsEmpty (((⊥ : X.Opens) : Scheme.{0}) : Type) := by
    change IsEmpty ((⊥ : X.Opens) : Set X); simp
  have hfree := etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme R ((⊥ : X.Opens) : Scheme.{0})
  have hN : IsZero ((chainsN R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro j
    refine IsZero.eq_of_src ?_ _ _
    exact hfree
  have hC : IsZero ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) :=
    Functor.map_isZero (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) hN
  have hX : ∀ p, IsZero (((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))).X p) := fun p =>
    Functor.map_isZero (HomologicalComplex.eval _ _ p) hC
  have : Subsingleton (Cochain ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n) :=
    ⟨fun a b => Cochain.ext _ _ fun p q hpq => (hX p).eq_of_src _ _⟩
  have : Subsingleton (Cocycle ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  change Subsingleton (CohomologyClass _ _ n)
  unfold CohomologyClass
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [Subsingleton.elim a b]

end LateralTheory.E.E8

end
