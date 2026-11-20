import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasic
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscChains

def heExt {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] {K L : ChainComplex C ℕ}
    (h : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingDownNat) (L.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap h.hom _
  inv := HomologicalComplex.extendMap h.inv _
  homotopyHomInvId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((h.homotopyHomInvId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((h.homotopyInvHomId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

variable (R : Type) [CommRing R]

def heN (P : PSh) :
    HomotopyEquiv ((chainsN R).obj (disc.obj P)) ((ChainComplex.single₀ (Shv R)).obj ((free R).obj P)) :=
  (HomotopyEquiv.ofIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).mapIso
      (Functor.constComp _ P (free R)))).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const ((free R).obj P)).homotopyEquiv

/- English proof (translation)
Simplify using `[heN, HomotopyEquiv.trans, HomotopyEquiv.ofIso, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv]`. Use `erw [HomologicalComplex.comp_f]`. Use `erw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]`. Simplify using the standard rewrite rules. Conclude with `Category.comp_id _`.
-/
lemma heN_inv_f_zero (P : PSh) :
    (heN R P).inv.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom := by
  dsimp [heN, HomotopyEquiv.trans, HomotopyEquiv.ofIso, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv]
  erw [HomologicalComplex.comp_f]
  erw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  simp
  exact Category.comp_id _

def he (P : PSh) : HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)) :=
  (HomotopyEquiv.ofIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat ((free R).obj P) 0 0
      (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).symm).trans
    (heExt (heN R P)).symm

/- English proof (translation)
Simplify using `[he, heExt, HomotopyEquiv.trans, HomotopyEquiv.symm, HomotopyEquiv.ofIso]`. Use `erw [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f, HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl), heN_inv_f_zero]`. Rewrite using `[sglι, chainsXIso]`. Use `erw [Category.assoc, Category.assoc]`. Use `erw [Iso.inv_hom_id_assoc]`.

Use `erw [Iso.inv_hom_id_assoc]`. Use `erw [Iso.inv_hom_id_assoc]`.
-/
lemma he_hom_f_zero (P : PSh) : sglι _ ≫ (he R P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv := by
  dsimp [he, heExt, HomotopyEquiv.trans, HomotopyEquiv.symm, HomotopyEquiv.ofIso]
  erw [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl), heN_inv_f_zero]
  rw [sglι, chainsXIso]
  erw [Category.assoc, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Iso.inv_hom_id_assoc]

end GlobalTheory.EtC.DiscChains

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `R _`. Use `⟨DiscChains.he R, DiscChains.he_hom_f_zero R, fun {P Q} f => ?_⟩` and prove the remaining obligations. Take `⟨-, hnat, -⟩` from `GlobalTheory.EtC.chains_basic R`. Apply `HomologicalComplex.from_single_hom_ext` to reduce the goal to its premises. Apply `(Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((free R).obj P)) _ _).1` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `sglι _ ≫ _ = sglι _ ≫ _`. Establish `e1 : ((DiscChains.he R P).hom ≫ (chains R).map (disc.map f)).f 0 = (DiscChains.he R P).hom.f 0 ≫ ((chains R).map (disc.map f)).f 0` using `HomologicalComplex.comp_f _ _ _`. Establish `e2 : ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (DiscChains.he R Q).hom).f 0 = ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 ≫ (DiscChains.he R Q).hom.f 0` using `HomologicalComplex.comp_f _ _ _`. Rewrite using `[e1, e2, ← Category.assoc, DiscChains.he_hom_f_zero]`. Establish `h1 : sglι ((free R).obj P) ≫ ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 = (free R).map f ≫ sglι ((free R).obj Q)`.

Express the relevant statement in the definitionally equal form `_ ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)).f 0 = _`. Rewrite using `[HomologicalComplex.single_map_f_self]`. Use `erw [Iso.inv_hom_id_assoc]`. Rewrite using `[← Category.assoc, h1, Category.assoc, DiscChains.he_hom_f_zero]`. Rewrite using `[← cancel_mono (chainsXIso R (disc.obj Q) 0).hom]`.

Establish `h2` using `hnat (disc.map f) 0`. Simplify using `only [Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Use `erw [h2]`. Simplify using the standard rewrite rules.
-/
theorem chains_disc_homotopyEquiv : ∀ (R : Type) [CommRing R] , ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)), (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧ ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) = (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom := by
  intro R _
  refine ⟨DiscChains.he R, DiscChains.he_hom_f_zero R, fun {P Q} f => ?_⟩
  obtain ⟨-, hnat, -⟩ := GlobalTheory.EtC.chains_basic R
  apply HomologicalComplex.from_single_hom_ext
  apply (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((free R).obj P)) _ _).1
  change sglι _ ≫ _ = sglι _ ≫ _
  have e1 : ((DiscChains.he R P).hom ≫ (chains R).map (disc.map f)).f 0 =
      (DiscChains.he R P).hom.f 0 ≫ ((chains R).map (disc.map f)).f 0 := HomologicalComplex.comp_f _ _ _
  have e2 : ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (DiscChains.he R Q).hom).f 0 =
      ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 ≫ (DiscChains.he R Q).hom.f 0 :=
    HomologicalComplex.comp_f _ _ _
  rw [e1, e2, ← Category.assoc, DiscChains.he_hom_f_zero]
  have h1 : sglι ((free R).obj P) ≫ ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 =
      (free R).map f ≫ sglι ((free R).obj Q) := by
    change _ ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    erw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h1, Category.assoc, DiscChains.he_hom_f_zero]
  rw [← cancel_mono (chainsXIso R (disc.obj Q) 0).hom]
  have h2 := hnat (disc.map f) 0
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [h2]
  simp

end GlobalTheory.EtC
