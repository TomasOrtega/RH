import Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Apply `(sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _ |>.injective` to reduce the goal to its premises. Use extensionality with `T : 2`. Distinguish the cases in `hT : IsEmpty T.unop`. Use `haveI := hT`.

Conclude with `((Sheaf.isTerminalOfBotCover _ T.unop (AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology T.unop)).isZero).eq_of_tgt _ _`. Rewrite `hT` using `[not_isEmpty_iff]`. Take `⟨t⟩` from `hT`. Establish `hP : IsEmpty ((yoneda.obj E).obj T)` using `⟨fun f => isEmptyElim (f.base t)⟩`. Apply `IsZero.eq_of_src` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `IsZero ((ModuleCat.free (ULift.{1} R)).obj (ULift.{1} ((yoneda.obj E).obj T)))`. Rewrite using `[ModuleCat.isZero_iff_subsingleton]`. Use `haveI : IsEmpty (ULift.{1} ((yoneda.obj E).obj T)) := inferInstance`. Express the relevant statement in the definitionally equal form `Subsingleton (ULift.{1} ((yoneda.obj E).obj T) →₀ ULift.{1} R)`. Use `infer_instance`.
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
Introduce `R _ X F n`. Establish `hE : IsEmpty (((⊥ : X.Opens) : Scheme.{0}) : Type)`. Express the relevant statement in the definitionally equal form `IsEmpty ((⊥ : X.Opens) : Set X)`. Simplify using the standard rewrite rules. Establish `hfree` using `etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme R ((⊥ : X.Opens) : Scheme.{0})`.

Establish `hN : IsZero ((chainsN R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0})))`. Rewrite using `[IsZero.iff_id_eq_zero]`. Apply `HomologicalComplex.hom_ext` to reduce the goal to its premises. Introduce `j`. Use `IsZero.eq_of_src ?_ _ _` and prove the remaining obligations.

Conclude with `hfree`. Establish `hC : IsZero ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0})))` using `Functor.map_isZero (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) hN`. Establish `hX : ∀ p, IsZero (((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))).X p)` using `fun p => Functor.map_isZero (HomologicalComplex.eval _ _ p) hC`. Establish `: Subsingleton (Cochain ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n)` using `⟨fun a b => Cochain.ext _ _ fun p q hpq => (hX p).eq_of_src _ _⟩`. Establish `: Subsingleton (Cocycle ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n)` using `⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩`.

Express the relevant statement in the definitionally equal form `Subsingleton (CohomologyClass _ _ n)`. Unfold `CohomologyClass`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `QuotientAddGroup.mk_surjective a`. Take `⟨b, rfl⟩` from `QuotientAddGroup.mk_surjective b`.

Rewrite using `[Subsingleton.elim a b]`.
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
