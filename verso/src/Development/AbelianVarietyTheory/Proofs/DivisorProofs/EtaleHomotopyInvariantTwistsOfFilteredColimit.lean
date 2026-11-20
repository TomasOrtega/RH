import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.PolyColim

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0})

def polyDiag : J ⥤ CommRingCat.{0} where
  obj j := CommRingCat.of (Polynomial (D.obj j))
  map f := CommRingCat.ofHom (Polynomial.mapRingHom (D.map f).hom)
  map_id j := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp [Polynomial.map_map]

def polyCocone (c : Cocone D) : Cocone (polyDiag D) where
  pt := CommRingCat.of (Polynomial c.pt)
  ι :=
    { app := fun j => CommRingCat.ofHom (Polynomial.mapRingHom (c.ι.app j).hom)
      naturality := fun i j f => by
        refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
        exact (Polynomial.map_map (D.map f).hom (c.ι.app j).hom (show Polynomial (D.obj i) from p)).trans
          (congrArg (fun g => Polynomial.map g (show Polynomial (D.obj i) from p))
            (by rw [← CommRingCat.hom_comp, c.w f])) }

variable {D} [IsFiltered J]

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
/- English proof (translation)
Take `⟨k, f, g, hfg⟩` from `Concrete.isColimit_exists_of_rep_eq D hc x 0 (by simpa using h)`. Conclude with `⟨k, f, by simpa using hfg⟩`.
-/
private lemma exists_map_eq_zero_of_isColimit_lemma {c : Cocone D} (hc : IsColimit c) {j : J}
    (x : D.obj j) (h : (c.ι.app j).hom x = 0) : ∃ (k : J) (f : j ⟶ k), (D.map f).hom x = 0 := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc x 0 (by simpa using h)
  exact ⟨k, f, by simpa using hfg⟩

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
/- English proof (translation)
Establish `key : ∀ s : Finset ℕ, ∃ (k : J) (f : j ⟶ k), ∀ n ∈ s, (D.map f).hom (p.coeff n) = 0`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨j, 𝟙 j, by simp⟩`. Consider the case `insert a s _ ih`.

Take `⟨k, f, hf⟩` from `ih`. Establish `ha : (c.ι.app k).hom ((D.map f).hom (p.coeff a)) = 0`. Rewrite using `[← CommRingCat.comp_apply, c.w f, ← Polynomial.coeff_map, h, Polynomial.coeff_zero]`. Take `⟨k', f', hf'⟩` from `exists_map_eq_zero_of_isColimit_lemma hc _ ha`. Use `⟨k', f ≫ f', fun n hn => ?_⟩` and prove the remaining obligations.

Rewrite using `[D.map_comp, CommRingCat.comp_apply]`. Break down `Finset.mem_insert.mp hn with rfl | hn` into its components or cases. Conclude with `hf'`. Rewrite using `[hf n hn, map_zero]`. Take `⟨k, f, hf⟩` from `key p.support`.

Use `⟨k, f, Polynomial.ext fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_map, Polynomial.coeff_zero]`. Distinguish the cases in `hn : n ∈ p.support`. Conclude with `hf n hn`. Rewrite using `[Polynomial.notMem_support_iff.mp hn, map_zero]`.
-/
theorem _root_.GlobalTheory.EtC.PolyColim.poly_exists_map_eq_zero {c : Cocone D} (hc : IsColimit c) {j : J}
    (p : Polynomial (D.obj j))
    (h : p.map (c.ι.app j).hom = 0) : ∃ (k : J) (f : j ⟶ k), p.map (D.map f).hom = 0 := by
  have key : ∀ s : Finset ℕ, ∃ (k : J) (f : j ⟶ k), ∀ n ∈ s, (D.map f).hom (p.coeff n) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨j, 𝟙 j, by simp⟩
    | insert a s _ ih =>
      obtain ⟨k, f, hf⟩ := ih
      have ha : (c.ι.app k).hom ((D.map f).hom (p.coeff a)) = 0 := by
        rw [← CommRingCat.comp_apply, c.w f, ← Polynomial.coeff_map, h, Polynomial.coeff_zero]
      obtain ⟨k', f', hf'⟩ := exists_map_eq_zero_of_isColimit_lemma hc _ ha
      refine ⟨k', f ≫ f', fun n hn => ?_⟩
      rw [D.map_comp, CommRingCat.comp_apply]
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact hf'
      · rw [hf n hn, map_zero]
  obtain ⟨k, f, hf⟩ := key p.support
  refine ⟨k, f, Polynomial.ext fun n => ?_⟩
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  by_cases hn : n ∈ p.support
  · exact hf n hn
  · rw [Polynomial.notMem_support_iff.mp hn, map_zero]

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
/- English proof (translation)
Take `⟨j, y, hy⟩` from `Concrete.isColimit_exists_rep D hc x`. Conclude with `⟨j, y, hy⟩`.
-/
private lemma exists_rep_of_isColimit_lemma_2 {c : Cocone D} (hc : IsColimit c) (x : c.pt) :
    ∃ (j : J) (y : D.obj j), (c.ι.app j).hom y = x := by
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep D hc x
  exact ⟨j, y, hy⟩

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Take `⟨i, y, hy⟩` from `hp`. Take `⟨j, z, hz⟩` from `hq`. Use `⟨IsFiltered.max i j, y.map (D.map (IsFiltered.leftToMax i j)).hom + z.map (D.map (IsFiltered.rightToMax i j)).hom, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.map_add, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, c.w, c.w, hy, hz]`. Consider the case `monomial n a`. Take `⟨j, y, hy⟩` from `exists_rep_of_isColimit_lemma_2 hc a`. Conclude with `⟨j, Polynomial.monomial n y, by rw [Polynomial.map_monomial, hy]⟩`.
-/
theorem _root_.GlobalTheory.EtC.PolyColim.poly_exists_rep {c : Cocone D} (hc : IsColimit c)
    (p : Polynomial c.pt) :
    ∃ (j : J) (y : Polynomial (D.obj j)), y.map (c.ι.app j).hom = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨i, y, hy⟩ := hp
    obtain ⟨j, z, hz⟩ := hq
    refine ⟨IsFiltered.max i j, y.map (D.map (IsFiltered.leftToMax i j)).hom +
      z.map (D.map (IsFiltered.rightToMax i j)).hom, ?_⟩
    rw [Polynomial.map_add, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, c.w, c.w, hy, hz]
  | monomial n a =>
    obtain ⟨j, y, hy⟩ := exists_rep_of_isColimit_lemma_2 hc a
    exact ⟨j, Polynomial.monomial n y, by rw [Polynomial.map_monomial, hy]⟩

def polyCoconeIsColimit {c : Cocone D} (hc : IsColimit c) : IsColimit (polyCocone D c) := by
  haveI : ReflectsColimitsOfShape J (forget CommRingCat.{0}) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (polyCocone D c)) ?_ ?_)
  · intro x
    obtain ⟨j, y, hy⟩ := poly_exists_rep hc (show Polynomial c.pt from x)
    exact ⟨j, y, hy.symm⟩
  · intro i j xi xj h
    change Polynomial.map (c.ι.app i).hom xi = Polynomial.map (c.ι.app j).hom xj at h
    obtain ⟨k, f, hf⟩ := poly_exists_map_eq_zero hc (j := IsFiltered.max i j)
      ((show Polynomial (D.obj i) from xi).map (D.map (IsFiltered.leftToMax i j)).hom -
        (show Polynomial (D.obj j) from xj).map (D.map (IsFiltered.rightToMax i j)).hom) (by
        rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
          ← CommRingCat.hom_comp, c.w, c.w, h, sub_self])
    refine ⟨k, IsFiltered.leftToMax i j ≫ f, IsFiltered.rightToMax i j ≫ f, ?_⟩
    change Polynomial.map (D.map (IsFiltered.leftToMax i j ≫ f)).hom xi =
      Polynomial.map (D.map (IsFiltered.rightToMax i j ≫ f)).hom xj
    rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp, sub_eq_zero] at hf
    exact hf

end GlobalTheory.EtC.PolyColim

namespace GlobalTheory.EtC

/- English proof (translation)
Use `show pull R (sch.map _) F n x = _`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp, pull_comp]`.
-/
theorem pull_spMap_comp (R : Type) [CommRing R] {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (F : Shv R) (n : ℤ) (x : H R (sp A) F n) :
    pull R (spMap (g.comp f)) F n x = pull R (spMap g) F n (pull R (spMap f) F n x) := by
  show pull R (sch.map _) F n x = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp, pull_comp]

/- English proof (translation)
Use `show sch.map _ = sch.map _ ≫ sch.map _`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]`.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show sch.map _ = sch.map _ ≫ sch.map _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

/- English proof (translation)
Introduce `q _ J _ _ D c hc hq hH i n`. Establish `hB : B1` using `pairingProperties`. Set `D'` to `PolyColim.polyDiag D`. Set `c'` to `PolyColim.polyCocone D c`. Establish `hc' : IsColimit c'` using `PolyColim.polyCoconeIsColimit hc`.

Take `⟨j0⟩ : Nonempty J` from `IsFiltered.nonempty`. Establish `hqc : IsUnit (q : c.pt)`. Use `(hq j0).map (c.ι.app j0).hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hqP : ∀ j, IsUnit (q : D'.obj j)` using `fun j => by`.

Use `(hq j).map (Polynomial.C : D.obj j →+* Polynomial (D.obj j))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hqc' : IsUnit (q : c'.pt)`. Use `hqc.map (Polynomial.C : c.pt →+* Polynomial c.pt)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `sq : ∀ j, (c'.ι.app j).hom.comp (Polynomial.C : D.obj j →+* Polynomial (D.obj j)) = (Polynomial.C : c.pt →+* Polynomial c.pt).comp (c.ι.app j).hom` using `fun j => RingHom.ext fun a => by`. Express the relevant statement in the definitionally equal form `Polynomial.map (c.ι.app j).hom (Polynomial.C a) = Polynomial.C ((c.ι.app j).hom a)`. Conclude with `Polynomial.map_C _`. Establish `sqD : ∀ {j k : J} (f : j ⟶ k), (D'.map f).hom.comp (Polynomial.C : D.obj j →+* Polynomial (D.obj j)) = (Polynomial.C : D.obj k →+* Polynomial (D.obj k)).comp (D.map f).hom` using `@fun j k f => RingHom.ext fun a => by`. Express the relevant statement in the definitionally equal form `Polynomial.map (D.map f).hom (Polynomial.C a) = Polynomial.C ((D.map f).hom a)`.

Conclude with `Polynomial.map_C _`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨j, y, rfl⟩` from `(hB q D c hc n i).1 x hqc`.

Establish `e1 : pull _ (spMap (c'.ι.app j).hom) _ _ (pull _ (spMap (Polynomial.C : D.obj j →+* Polynomial (D.obj j))) _ _ y) = 0` using `(pull_spMap_comp (ZMod q) Polynomial.C (c'.ι.app j).hom (tw q i) n y).symm.trans ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y) (sq j)).trans ((pull_spMap_comp (ZMod q) (c.ι.app j).hom Polynomial.C (tw q i) n y).trans hx))`. Take `⟨k, f, hf⟩` from `(hB q D' c' hc' n i).2 j _ (hqP j) e1`. Establish `e2 : pull _ (spMap (Polynomial.C : D.obj k →+* Polynomial (D.obj k))) _ _ (pull _ (spMap (D.map f).hom) _ _ y) = 0` using `(pull_spMap_comp (ZMod q) (D.map f).hom Polynomial.C (tw q i) n y).symm.trans ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y) (sqD f).symm).trans ((pull_spMap_comp (ZMod q) Polynomial.C (D'.map f).hom (tw q i) n y).trans hf))`. Establish `e3` using `(hH k i n).1 (e2.trans (map_zero _).symm)`. Rewrite using `[← c.w f, CommRingCat.hom_comp, spMap_comp', pull_comp, e3, map_zero]`.

Introduce `x`. Take `⟨j, y, rfl⟩` from `(hB q D' c' hc' n i).1 x hqc'`. Take `⟨y', rfl⟩` from `(hH j i n).2 y`. Use `⟨pull _ (spMap (c.ι.app j).hom) _ _ y', ?_⟩` and prove the remaining obligations. Conclude with `(pull_spMap_comp (ZMod q) (c.ι.app j).hom Polynomial.C (tw q i) n y').symm.trans ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y') (sq j).symm).trans (pull_spMap_comp (ZMod q) Polynomial.C (c'.ι.app j).hom (tw q i) n y'))`.
-/
theorem hInv_of_filtered_colimit : ∀ (q : ℕ) [NeZero q] (J : Type) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ j, IsUnit (q : D.obj j)) →
    (∀ j, HInv q (D.obj j)) → HInv q c.pt := by
  intro q _ J _ _ D c hc hq hH i n
  have hB : B1 := pairingProperties
  let D' := PolyColim.polyDiag D
  let c' := PolyColim.polyCocone D c
  have hc' : IsColimit c' := PolyColim.polyCoconeIsColimit hc
  obtain ⟨j0⟩ : Nonempty J := IsFiltered.nonempty
  have hqc : IsUnit (q : c.pt) := by
    have := (hq j0).map (c.ι.app j0).hom
    rwa [map_natCast] at this
  have hqP : ∀ j, IsUnit (q : D'.obj j) := fun j => by
    have := (hq j).map (Polynomial.C : D.obj j →+* Polynomial (D.obj j))
    rwa [map_natCast] at this
  have hqc' : IsUnit (q : c'.pt) := by
    have := hqc.map (Polynomial.C : c.pt →+* Polynomial c.pt)
    rwa [map_natCast] at this
  have sq : ∀ j, (c'.ι.app j).hom.comp (Polynomial.C : D.obj j →+* Polynomial (D.obj j)) =
      (Polynomial.C : c.pt →+* Polynomial c.pt).comp (c.ι.app j).hom := fun j =>
    RingHom.ext fun a => by
      change Polynomial.map (c.ι.app j).hom (Polynomial.C a) = Polynomial.C ((c.ι.app j).hom a)
      exact Polynomial.map_C _
  have sqD : ∀ {j k : J} (f : j ⟶ k), (D'.map f).hom.comp (Polynomial.C : D.obj j →+* Polynomial (D.obj j)) =
      (Polynomial.C : D.obj k →+* Polynomial (D.obj k)).comp (D.map f).hom := @fun j k f =>
    RingHom.ext fun a => by
      change Polynomial.map (D.map f).hom (Polynomial.C a) = Polynomial.C ((D.map f).hom a)
      exact Polynomial.map_C _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, rfl⟩ := (hB q D c hc n i).1 x hqc
    have e1 : pull _ (spMap (c'.ι.app j).hom) _ _ (pull _ (spMap (Polynomial.C : D.obj j →+* Polynomial (D.obj j))) _ _ y) = 0 :=
      (pull_spMap_comp (ZMod q) Polynomial.C (c'.ι.app j).hom (tw q i) n y).symm.trans
        ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y) (sq j)).trans
          ((pull_spMap_comp (ZMod q) (c.ι.app j).hom Polynomial.C (tw q i) n y).trans hx))
    obtain ⟨k, f, hf⟩ := (hB q D' c' hc' n i).2 j _ (hqP j) e1
    have e2 : pull _ (spMap (Polynomial.C : D.obj k →+* Polynomial (D.obj k))) _ _ (pull _ (spMap (D.map f).hom) _ _ y) = 0 :=
      (pull_spMap_comp (ZMod q) (D.map f).hom Polynomial.C (tw q i) n y).symm.trans
        ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y) (sqD f).symm).trans
          ((pull_spMap_comp (ZMod q) Polynomial.C (D'.map f).hom (tw q i) n y).trans hf))
    have e3 := (hH k i n).1 (e2.trans (map_zero _).symm)
    rw [← c.w f, CommRingCat.hom_comp, spMap_comp', pull_comp, e3, map_zero]
  · intro x
    obtain ⟨j, y, rfl⟩ := (hB q D' c' hc' n i).1 x hqc'
    obtain ⟨y', rfl⟩ := (hH j i n).2 y
    refine ⟨pull _ (spMap (c.ι.app j).hom) _ _ y', ?_⟩
    exact (pull_spMap_comp (ZMod q) (c.ι.app j).hom Polynomial.C (tw q i) n y').symm.trans
      ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y') (sq j).symm).trans
        (pull_spMap_comp (ZMod q) Polynomial.C (c'.ι.app j).hom (tw q i) n y'))

end GlobalTheory.EtC

end
