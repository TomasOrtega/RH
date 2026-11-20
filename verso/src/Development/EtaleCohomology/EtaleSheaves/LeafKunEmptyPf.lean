import Development.EtaleCohomology.EtaleSheaves.LeafKunGlobalCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.LeafKunEmptyPf

variable {R : Type} [CommRing R]

/- English proof (translation)
The claim follows from `ModuleCat.isZero_iff_subsingleton.mp (Sheaf.isTerminalOfBotCover F U (Scheme.bot_mem_grothendieckTopology U)).isZero`.
-/
theorem sec_sub (F : Shv R) (U : Scheme.{0}) [IsEmpty U] : Subsingleton (Sec F U) :=
  ModuleCat.isZero_iff_subsingleton.mp (Sheaf.isTerminalOfBotCover F U (Scheme.bot_mem_grothendieckTopology U)).isZero

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `α β`. Apply `NatTrans.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `U`. Apply `ModuleCat.hom_ext` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Distinguish the cases in `h : IsEmpty ((Opposite.unop U : Scheme.{0}) : Type)`. Use `haveI := hM _ h`. Conclude with `Subsingleton.elim _ _`.

Use `haveI : IsEmpty (Opposite.unop U ⟶ Z) := ⟨fun f => h ⟨fun y => isEmptyElim (f.base y)⟩⟩`. Establish `hs : Subsingleton (((freeP R).obj (yoneda.obj Z)).obj U)`. Express the relevant statement in the definitionally equal form `Subsingleton (ULift.{1} (Opposite.unop U ⟶ Z) →₀ ULift.{1} R)`. Use `infer_instance`. Rewrite using `[Subsingleton.elim x 0, map_zero, map_zero]`.
-/
theorem subsingleton_freePresheaf_hom_of_isEmpty (Z : Scheme.{0}) [IsEmpty Z] (M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (hM : ∀ U : Scheme.{0}, IsEmpty U → Subsingleton (M.obj (op U))) :
    Subsingleton ((freeP R).obj (yoneda.obj Z) ⟶ M) := by
  constructor; intro α β
  apply NatTrans.ext; funext U
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  by_cases h : IsEmpty ((Opposite.unop U : Scheme.{0}) : Type)
  · haveI := hM _ h; exact Subsingleton.elim _ _
  · haveI : IsEmpty (Opposite.unop U ⟶ Z) := ⟨fun f => h ⟨fun y => isEmptyElim (f.base y)⟩⟩
    have hs : Subsingleton (((freeP R).obj (yoneda.obj Z)).obj U) := by
      change Subsingleton (ULift.{1} (Opposite.unop U ⟶ Z) →₀ ULift.{1} R); infer_instance
    rw [Subsingleton.elim x 0, map_zero, map_zero]

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Establish `h1` using `subsingleton_freePresheaf_hom_of_isEmpty (R := R) Z ((sheafToPresheaf Scheme.etaleTopology _).obj ((free R).obj (yoneda.obj Z))) (fun U hU => by haveI := hU; exact sec_sub _ U)`. Apply `((sheafificationAdjunction Scheme.etaleTopology _).homEquiv ((freeP R).obj (yoneda.obj Z)) ((free R).obj (yoneda.obj Z))).injective` to reduce the goal to its premises. Conclude with `h1.elim _ _`.
-/
theorem free_zero (Z : Scheme.{0}) [IsEmpty Z] : IsZero ((free R).obj (yoneda.obj Z)) := by
  rw [IsZero.iff_id_eq_zero]
  have h1 := subsingleton_freePresheaf_hom_of_isEmpty (R := R) Z ((sheafToPresheaf Scheme.etaleTopology _).obj ((free R).obj (yoneda.obj Z)))
    (fun U hU => by haveI := hU; exact sec_sub _ U)
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv ((freeP R).obj (yoneda.obj Z))
    ((free R).obj (yoneda.obj Z))).injective
  exact h1.elim _ _

/- English proof (translation)
Distinguish the cases in `h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = p`. Take `⟨j, hj⟩` from `h`. Establish `hz : IsZero (((chainsN R).obj (sch.obj Z)).X j)` using `free_zero (R := R) Z`. Conclude with `hz.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat hj)`. Use `push Not at h`.

Conclude with `HomologicalComplex.isZero_extend_X ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat p h`.
-/
theorem chains_zero (Z : Scheme.{0}) [IsEmpty Z] (p : ℤ) : IsZero (((chains R).obj (sch.obj Z)).X p) := by
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = p
  · obtain ⟨j, hj⟩ := h
    have hz : IsZero (((chainsN R).obj (sch.obj Z)).X j) := free_zero (R := R) Z
    exact hz.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat hj)
  · push Not at h
    exact HomologicalComplex.isZero_extend_X ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat p h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y`. Take `⟨a, rfl⟩` from `CohomologyClass.mk_surjective x`. Take `⟨b, rfl⟩` from `CohomologyClass.mk_surjective y`. Use `congr 1`.

Apply `Cocycle.ext` to reduce the goal to its premises. Apply `Cochain.ext` to reduce the goal to its premises. Introduce `p q hpq`. Conclude with `(chains_zero (R := R) Z p).eq_of_src _ _`.
-/
theorem H_sub (Z : Scheme.{0}) [IsEmpty Z] (F : Shv R) (n : ℤ) : Subsingleton (H R (sch.obj Z) F n) := by
  constructor; intro x y
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective y
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  exact (chains_zero (R := R) Z p).eq_of_src _ _

instance botEmpty {X : Scheme.{0}} : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x => by
  have h : (⊥ : X.Opens).ι.base x ∈ Set.range (⊥ : X.Opens).ι.base := ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι] at h; simp at h⟩

end LateralTheory.E.LeafKunEmptyPf
