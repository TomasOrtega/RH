import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceDescentLocalEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringsRefineOfCechConervePropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEtaleCechNerveResolutionOfSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceOfStrictlyHenselianStaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

private def covE (S : Scheme.{0}) : MorphismProperty (S.Etale)ᵒᵖ := fun _ _ g => Surjective g.unop.left

private instance (S : Scheme.{0}) : (covE S).IsStableUnderComposition where
  comp_mem f g hf hg := by
    have hf' : Surjective f.unop.left := hf
    have hg' : Surjective g.unop.left := hg
    change Surjective (f ≫ g).unop.left
    have : (f ≫ g).unop.left = g.unop.left ≫ f.unop.left := rfl
    rw [this]
    infer_instance

private noncomputable def etHom {S : Scheme.{0}} (U : (S.Etale)ᵒᵖ) (V : Over S) (hV : Etale V.hom)
    (h : V ⟶ (Scheme.Etale.forget S).obj U.unop) :
    U ⟶ op (@Scheme.Etale.mk S _ V.hom hV) :=
  ((Scheme.Etale.forget S).preimage
    (X := @Scheme.Etale.mk S _ V.hom hV) (Y := U.unop) h).op

/- English proof (translation)
The claim follows from `(Scheme.Etale.forget S).map_preimage (X := @Scheme.Etale.mk S _ V.hom hV) (Y := U.unop) h`.
-/
private theorem etHom_map {S : Scheme.{0}} (U : (S.Etale)ᵒᵖ) (V : Over S) (hV : Etale V.hom)
    (h : V ⟶ (Scheme.Etale.forget S).obj U.unop) :
    (Scheme.Etale.forget S).map (etHom U V hV h).unop = h :=
  (Scheme.Etale.forget S).map_preimage
    (X := @Scheme.Etale.mk S _ V.hom hV) (Y := U.unop) h

/- English proof (translation)
Conclude with `congrArg (fun k => k.left) (etHom_map U V hV h)`.
-/
private theorem etHom_left {S : Scheme.{0}} (U : (S.Etale)ᵒᵖ) (V : Over S) (hV : Etale V.hom)
    (h : V ⟶ (Scheme.Etale.forget S).obj U.unop) : (etHom U V hV h).unop.left = h.left := by
  exact congrArg (fun k => k.left) (etHom_map U V hV h)

/- English proof (translation)
Establish `: IsIso (sch.map (Over.mk (𝟙 S)).hom)`. Express the relevant statement in the definitionally equal form `IsIso (sch.map (𝟙 S))`. Rewrite using `[sch.map_id]`. Use `infer_instance`. Use `infer_instance`.
-/
private theorem fst_iso (E : Spc) (S : Scheme.{0}) (p : E ⟶ sch.obj S) :
    IsIso (pullback.fst p (sch.map (Over.mk (𝟙 S)).hom)) := by
  have : IsIso (sch.map (Over.mk (𝟙 S)).hom) := by
    change IsIso (sch.map (𝟙 S))
    rw [sch.map_id]
    infer_instance
  infer_instance

/- English proof (translation)
Introduce `R _ F S E E' α p hF hq hq' hst`. Establish `key` using `GlobalTheory.T.etale_cohomology_equivalence_of_strictly_henselian_stalks R F S E E' α p hF hq hq' hst`. Establish `basic` using `GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F`. Set `Φ : (S.Etale)ᵒᵖ ⥤ Spcᵒᵖ` to `(Scheme.Etale.forget S ⋙ bc (α ≫ p)).op`. Set `Φ' : (S.Etale)ᵒᵖ ⥤ Spcᵒᵖ` to `(Scheme.Etale.forget S ⋙ bc p).op`.

Set `β : Φ' ⟶ Φ` to `NatTrans.op (Functor.whiskerLeft (Scheme.Etale.forget S) (bcMap α p))`. Establish `hall : ∀ U, Eqv R (β.app U).unop F`. Use `GlobalTheory.T.etaleSpace_descent_local_equivalence R F (S.Etale)ᵒᵖ (covE S) Φ Φ' β ?_ ?_ ?_` and prove the remaining obligations. Use `GlobalTheory.T.coveringsRefine_of_cechConerve_property (S.Etale)ᵒᵖ (covE S) _ ?_` and prove the remaining obligations. Introduce `U V g hg`.

Conclude with `⟨GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective R S E (α ≫ p) U V g hg, GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective R S E' p U V g hg⟩`. Introduce `U n x`. Take `⟨V, h, y, hV, hs, hy⟩` from `(key ((Scheme.Etale.forget S).obj U.unop) U.unop.prop n).1 x`. Use `⟨op (@Scheme.Etale.mk S _ V.hom hV), etHom U V hV h, ?_, y, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Surjective (etHom U V hV h).unop.left`.

Rewrite using `[etHom_left]`. Conclude with `hs`. Establish `hm : (Φ.map (etHom U V hV h)).unop = (bc (α ≫ p)).map h`. Express the relevant statement in the definitionally equal form `(bc (α ≫ p)).map ((Scheme.Etale.forget S).map (etHom U V hV h).unop) = _`. Rewrite using `[etHom_map]`.

Both sides reduce to the same expression. Rewrite using `[hm]`. Conclude with `hy`. Introduce `U n y hy`. Take `⟨V, h, hV, hs, hz⟩` from `(key ((Scheme.Etale.forget S).obj U.unop) U.unop.prop n).2 y hy`.

Use `⟨op (@Scheme.Etale.mk S _ V.hom hV), etHom U V hV h, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Surjective (etHom U V hV h).unop.left`. Rewrite using `[etHom_left]`. Conclude with `hs`. Establish `hm : (Φ'.map (etHom U V hV h)).unop = (bc p).map h`.

Express the relevant statement in the definitionally equal form `(bc p).map ((Scheme.Etale.forget S).map (etHom U V hV h).unop) = _`. Rewrite using `[etHom_map]`. Both sides reduce to the same expression. Rewrite using `[hm]`. Conclude with `hz`.

Establish `hid : Eqv R ((bcMap α p).app (Over.mk (𝟙 S))) F` using `hall (op (@Scheme.Etale.mk S S (𝟙 S) inferInstance))`. Establish `i1` using `fst_iso E S (α ≫ p)`. Establish `i2` using `fst_iso E' S p`. Establish `hsq : (bcMap α p).app (Over.mk (𝟙 S)) ≫ pullback.fst p (sch.map (Over.mk (𝟙 S)).hom) = pullback.fst (α ≫ p) (sch.map (Over.mk (𝟙 S)).hom) ≫ α`. Conclude with `pullback.lift_fst _ _ _`.

Establish `e1 : Eqv R (pullback.fst (α ≫ p) (sch.map (Over.mk (𝟙 S)).hom)) F` using `basic.1 _ _ _ i1`. Establish `e2 : Eqv R (pullback.fst p (sch.map (Over.mk (𝟙 S)).hom)) F` using `basic.1 _ _ _ i2`. Establish `e3` using `(basic.2.1 _ _ _ _ _).1 hid e2`. Rewrite `e3` using `[hsq]`. Conclude with `(basic.2.1 _ _ _ _ _).2.1 e1 e3`.
-/
theorem UpperTheory.Cb.equiv_of_stalkwise_base_change :
    ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → Eqv R α F := by
  intro R _ F S E E' α p hF hq hq' hst
  have key := GlobalTheory.T.etale_cohomology_equivalence_of_strictly_henselian_stalks R F S E E' α p hF hq hq' hst
  have basic := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  let Φ : (S.Etale)ᵒᵖ ⥤ Spcᵒᵖ := (Scheme.Etale.forget S ⋙ bc (α ≫ p)).op
  let Φ' : (S.Etale)ᵒᵖ ⥤ Spcᵒᵖ := (Scheme.Etale.forget S ⋙ bc p).op
  let β : Φ' ⟶ Φ := NatTrans.op (Functor.whiskerLeft (Scheme.Etale.forget S) (bcMap α p))
  have hall : ∀ U, Eqv R (β.app U).unop F := by
    refine GlobalTheory.T.etaleSpace_descent_local_equivalence R F (S.Etale)ᵒᵖ (covE S) Φ Φ' β ?_ ?_ ?_
    · refine GlobalTheory.T.coveringsRefine_of_cechConerve_property (S.Etale)ᵒᵖ (covE S) _ ?_
      intro U V g hg
      exact ⟨GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective R S E (α ≫ p) U V g hg, GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective R S E' p U V g hg⟩
    · intro U n x
      obtain ⟨V, h, y, hV, hs, hy⟩ := (key ((Scheme.Etale.forget S).obj U.unop) U.unop.prop n).1 x
      refine ⟨op (@Scheme.Etale.mk S _ V.hom hV), etHom U V hV h, ?_, y, ?_⟩
      · change Surjective (etHom U V hV h).unop.left
        rw [etHom_left]
        exact hs
      · have hm : (Φ.map (etHom U V hV h)).unop = (bc (α ≫ p)).map h := by
          change (bc (α ≫ p)).map ((Scheme.Etale.forget S).map (etHom U V hV h).unop) = _
          rw [etHom_map]
          rfl
        rw [hm]
        exact hy
    · intro U n y hy
      obtain ⟨V, h, hV, hs, hz⟩ := (key ((Scheme.Etale.forget S).obj U.unop) U.unop.prop n).2 y hy
      refine ⟨op (@Scheme.Etale.mk S _ V.hom hV), etHom U V hV h, ?_, ?_⟩
      · change Surjective (etHom U V hV h).unop.left
        rw [etHom_left]
        exact hs
      · have hm : (Φ'.map (etHom U V hV h)).unop = (bc p).map h := by
          change (bc p).map ((Scheme.Etale.forget S).map (etHom U V hV h).unop) = _
          rw [etHom_map]
          rfl
        rw [hm]
        exact hz
  have hid : Eqv R ((bcMap α p).app (Over.mk (𝟙 S))) F :=
    hall (op (@Scheme.Etale.mk S S (𝟙 S) inferInstance))
  have i1 := fst_iso E S (α ≫ p)
  have i2 := fst_iso E' S p
  have hsq : (bcMap α p).app (Over.mk (𝟙 S)) ≫ pullback.fst p (sch.map (Over.mk (𝟙 S)).hom) =
      pullback.fst (α ≫ p) (sch.map (Over.mk (𝟙 S)).hom) ≫ α := by
    exact pullback.lift_fst _ _ _
  have e1 : Eqv R (pullback.fst (α ≫ p) (sch.map (Over.mk (𝟙 S)).hom)) F := basic.1 _ _ _ i1
  have e2 : Eqv R (pullback.fst p (sch.map (Over.mk (𝟙 S)).hom)) F := basic.1 _ _ _ i2
  have e3 := (basic.2.1 _ _ _ _ _).1 hid e2
  rw [hsq] at e3
  exact (basic.2.1 _ _ _ _ _).2.1 e1 e3
