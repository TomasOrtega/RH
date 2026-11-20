import Development.EtaleCohomology.EtaleSheaves.UnitExistence

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneExistsPf.CocycleOfSec

def eta (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) : (freeP R).obj (E.obj (op (SimplexCategory.mk 0))) ⟶ F.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom (fun x => s U.unop ⟨ULift.down x⟩))
  naturality {U V} g := by
    apply ModuleCat.free_hom_ext
    intro x
    erw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (hs V.unop U.unop g.unop _ _).symm

/- English proof (translation)
Use `erw [ModuleCat.freeDesc_apply]`. Both sides reduce to the same expression.
-/
theorem eta_freeMk (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) (U : Scheme.{0}) (x : Sx E 0 U) :
    ((eta R F E s hs).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = s U ⟨x⟩ := by
  erw [ModuleCat.freeDesc_apply]
  rfl

/- English proof (translation)
Use `NatTrans.ext (funext fun U => ?_)` and prove the remaining obligations. Apply `ModuleCat.free_hom_ext` to reduce the goal to its premises. Introduce `x`. Use `erw [ModuleCat.comp_apply, ModuleCat.comp_apply]`. Use `erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]`.

Both sides reduce to the same expression.
-/
theorem eta_face (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) (i j : Fin 2) :
    (freeP R).map (E.δ i) ≫ eta R F E s hs = (freeP R).map (E.δ j) ≫ eta R F E s hs := by
  refine NatTrans.ext (funext fun U => ?_)
  apply ModuleCat.free_hom_ext
  intro x
  erw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
  rfl

def phi (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) : (free R).obj (E.obj (op (SimplexCategory.mk 0))) ⟶ F :=
  ⟨sheafifyLift Scheme.etaleTopology (eta R F E s hs) F.property⟩

/- English proof (translation)
Establish `h` using `toSheafify_sheafifyLift Scheme.etaleTopology (eta R F E s hs) F.property`. Establish `h2` using `congrArg (fun t => (t.app (op U)).hom (ModuleCat.freeMk (ULift.up x))) h`. Use `erw [eta_freeMk R F E s hs] at h2`. Conclude with `h2`.
-/
theorem phi_freeGen (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) (U : Scheme.{0}) (x : Sx E 0 U) :
    ((phi R F E s hs).hom.app (op U)).hom (freeGen R _ U x) = s U ⟨x⟩ := by
  have h := toSheafify_sheafifyLift Scheme.etaleTopology (eta R F E s hs) F.property
  have h2 := congrArg (fun t => (t.app (op U)).hom (ModuleCat.freeMk (ULift.up x))) h
  erw [eta_freeMk R F E s hs] at h2
  exact h2

/- English proof (translation)
Apply `Sheaf.hom_ext` to reduce the goal to its premises. Apply `sheafify_hom_ext _ _ _ F.property` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `toSheafify _ _ ≫ sheafifyMap _ ((freeP R).map (E.δ i)) ≫ sheafifyLift _ (eta R F E s hs) F.property = toSheafify _ _ ≫ sheafifyMap _ ((freeP R).map (E.δ j)) ≫ sheafifyLift _ (eta R F E s hs) F.property`. Rewrite using `[← Category.assoc, ← toSheafify_naturality, Category.assoc, toSheafify_sheafifyLift, ← Category.assoc, ← toSheafify_naturality, Category.assoc, toSheafify_sheafifyLift, eta_face R F E s hs i j]`.
-/
theorem phi_face (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) (i j : Fin 2) :
    (free R).map (E.δ i) ≫ phi R F E s hs = (free R).map (E.δ j) ≫ phi R F E s hs := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ F.property
  change toSheafify _ _ ≫ sheafifyMap _ ((freeP R).map (E.δ i)) ≫ sheafifyLift _ (eta R F E s hs) F.property =
    toSheafify _ _ ≫ sheafifyMap _ ((freeP R).map (E.δ j)) ≫ sheafifyLift _ (eta R F E s hs) F.property
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, toSheafify_sheafifyLift,
    ← Category.assoc, ← toSheafify_naturality, Category.assoc, toSheafify_sheafifyLift, eta_face R F E s hs i j]

/- English proof (translation)
Unfold `resι`. Use `erw [Category.assoc, HomologicalComplex.Hom.comm]`. Use `erw [show ((singleFunctor (Shv R) 0).obj F).d 0 1 = 0 from (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by norm_num)).eq_of_tgt _ _, zero_comp]`. Conclude with `Limits.comp_zero`.
-/
theorem resι_d (R : Type) [CommRing R] (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  unfold resι
  erw [Category.assoc, HomologicalComplex.Hom.comm]
  erw [show ((singleFunctor (Shv R) 0).obj F).d 0 1 = 0 from
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by norm_num)).eq_of_tgt _ _, zero_comp]
  exact Limits.comp_zero

def gmap (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) : ((chains R).obj E).X 0 ⟶ (res R F).X 0 :=
  (chainsXIso R E 0).hom ≫ phi R F E s hs ≫ resι R F

/- English proof (translation)
Use `erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]`. Rewrite using `[Fin.sum_univ_two]`. Use `erw [Preadditive.add_comp]`. Simplify using `only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, Preadditive.neg_comp]`. Use `erw [phi_face R F E s hs 0 1]`.

Use `erw [Preadditive.neg_comp]`. Conclude with `add_neg_cancel _`.
-/
theorem key (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) : ((chainsN R).obj E).d 1 0 ≫ phi R F E s hs = 0 := by
  erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  rw [Fin.sum_univ_two]
  erw [Preadditive.add_comp]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, Preadditive.neg_comp]
  erw [phi_face R F E s hs 0 1]
  erw [Preadditive.neg_comp]
  exact add_neg_cancel _

/- English proof (translation)
Rewrite using `[show ((chains R).obj E).d (-1) 0 = (chainsXIso R E 1).hom ≫ ((chainsN R).obj E).d 1 0 ≫ (chainsXIso R E 0).inv from HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := 1) (j := 0) rfl rfl]`. Establish `k` using `key R F E s hs`. Unfold `gmap`. Use `erw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]`. Establish `k2 : ((chainsN R).obj E).d 1 0 ≫ phi R F E s hs ≫ resι R F = 0` using `(Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ resι R F) k).trans zero_comp)`.

Conclude with `(congrArg (fun t => (chainsXIso R E 1).hom ≫ t) k2).trans Limits.comp_zero`.
-/
theorem chains_d (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) : ((chains R).obj E).d (-1) 0 ≫ gmap R F E s hs = 0 := by
  rw [show ((chains R).obj E).d (-1) 0 = (chainsXIso R E 1).hom ≫ ((chainsN R).obj E).d 1 0 ≫ (chainsXIso R E 0).inv from
    HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := 1) (j := 0) rfl rfl]
  have k := key R F E s hs
  unfold gmap
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  have k2 : ((chainsN R).obj E).d 1 0 ≫ phi R F E s hs ≫ resι R F = 0 :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ resι R F) k).trans zero_comp)
  exact (congrArg (fun t => (chainsXIso R E 1).hom ≫ t) k2).trans Limits.comp_zero

def alpha (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) : Cocycle ((chains R).obj E) (res R F) 0 :=
  Cocycle.mk (Cochain.single (gmap R F E s hs) 0) 1 (by norm_num) (by
    rw [Cochain.δ_single (gmap R F E s hs) 0 1 (by norm_num) (-1) 1 (by norm_num) (by norm_num)]
    have h1 : gmap R F E s hs ≫ (res R F).d 0 1 = 0 := by simp only [gmap, Category.assoc, resι_d R F, comp_zero]
    rw [h1, chains_d R F E s hs, Cochain.single_zero, Cochain.single_zero, smul_zero, add_zero])

/- English proof (translation)
Unfold `ev`. Use `erw [Cochain.single_v]`. Rewrite using `[gmap, Iso.inv_hom_id_assoc]`. Express the relevant statement in the definitionally equal form `((resι R F).hom.app (op U)).hom (((phi R F E s hs).hom.app (op U)).hom (freeGen R _ U x)) = _`. Rewrite using `[phi_freeGen R F E s hs]`.
-/
theorem alpha_ev (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) (U : Scheme.{0}) (x : Sx E 0 U) :
    ev (alpha R F E s hs).1 0 0 (by simp) U x = Sec.map (resι R F) (s U ⟨x⟩) := by
  unfold ev
  erw [Cochain.single_v]
  rw [gmap, Iso.inv_hom_id_assoc]
  change ((resι R F).hom.app (op U)).hom (((phi R F E s hs).hom.app (op U)).hom (freeGen R _ U x)) = _
  rw [phi_freeGen R F E s hs]

/- English proof (translation)
Introduce `R _ F E s hs` and use `⟨alpha R F E s hs, fun U x => alpha_ev R F E s hs U x⟩`.
-/
theorem leafCocycleOfSec_pf : LeafCocycleOfSec := fun R _ F E s hs =>
  ⟨alpha R F E s hs, fun U x => alpha_ev R F E s hs U x⟩

/- English proof (translation)
The claim follows from `LeafOneExists_of hU leafCocycleOfSec_pf`.
-/
theorem LeafOneExists_of_unit (hU : LeafUnitSec) : LateralTheory.E.LeafOneSpecPf.LeafOneExists :=
  LeafOneExists_of hU leafCocycleOfSec_pf

end LateralTheory.E.LeafOneExistsPf.CocycleOfSec
