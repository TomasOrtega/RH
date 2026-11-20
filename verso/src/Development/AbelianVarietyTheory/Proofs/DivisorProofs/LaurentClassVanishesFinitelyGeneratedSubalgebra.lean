import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitary
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.GmStep.KillColim

/- English proof (translation)
Rewrite using `[laurentMap_coeff, Finsupp.mapRange_apply]`.
-/
theorem laurentMap_coeff_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (p : LaurentPolynomial A) (m : ℤ) : (laurentMap f p).coeff m = f (p.coeff m) := by
  rw [laurentMap_coeff, Finsupp.mapRange_apply]

/- English proof (translation)
Use `RingHom.ext fun p => ?_` and prove the remaining obligations. Apply `AddMonoidAlgebra.coeff_injective` to reduce the goal to its premises. Use extensionality with `m`. Simplify using `[laurentMap_coeff_apply]`.
-/
theorem laurentMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (laurentMap g).comp (laurentMap f) = laurentMap (g.comp f) := by
  refine RingHom.ext fun p => ?_
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    simp [laurentMap_coeff_apply]

/- English proof (translation)
Use `RingHom.ext fun p => ?_` and prove the remaining obligations. Apply `AddMonoidAlgebra.coeff_injective` to reduce the goal to its premises. Use extensionality with `m`. Simplify using `[laurentMap_coeff_apply]`.
-/
theorem laurentMap_id (A : Type) [CommRing A] : laurentMap (RingHom.id A) = RingHom.id _ := by
  refine RingHom.ext fun p => ?_
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    simp [laurentMap_coeff_apply]

/- English proof (translation)
Introduce `p r h`. Apply `AddMonoidAlgebra.coeff_injective` to reduce the goal to its premises. Use extensionality with `m`. Apply `hf` to reduce the goal to its premises. Rewrite using `[← laurentMap_coeff_apply, ← laurentMap_coeff_apply, h]`.
-/
theorem laurentMap_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (laurentMap f) := by
  intro p r h
  apply AddMonoidAlgebra.coeff_injective
  ext m
  apply hf
  rw [← laurentMap_coeff_apply, ← laurentMap_coeff_apply, h]

/- English proof (translation)
Rewrite using `[← Functor.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

def diag : Finset S ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (LaurentPolynomial (Algebra.adjoin A (t : Set S)))
  map {t u} h := CommRingCat.ofHom
    (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 h.le))).toRingHom)
  map_id t := by
    ext1
    refine (Eq.trans ?_ (laurentMap_id _)).trans rfl
    congr 1
  map_comp f g := by
    ext1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [laurentMap_comp]
    rfl

def cocone : Cocone (diag A S) where
  pt := CommRingCat.of (LaurentPolynomial S)
  ι := { app := fun t => CommRingCat.ofHom (laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom)
         naturality := fun t u h => by
           ext1
           simp only [diag, Functor.const_obj_map, Category.comp_id, CommRingCat.hom_comp,
             CommRingCat.hom_ofHom]
           rw [laurentMap_comp]
           rfl }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cocone_ι_apply (t : Finset S) (p) :
    ((cocone A S).ι.app t).hom p = laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom p := rfl

/- English proof (translation)
Rewrite using `[map_mul, laurentMap_C, laurentMap_T]`. Both sides reduce to the same expression.
-/
theorem val_CT (t : Finset S) (a : Algebra.adjoin A (t : Set S)) (n : ℤ) :
    laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      LaurentPolynomial.C (a : S) * LaurentPolynomial.T n := by
  rw [map_mul, laurentMap_C, laurentMap_T]
  rfl

/- English proof (translation)
Use `show ((diag A S).map h ≫ (cocone A S).ι.app u).hom p = _`. Rewrite using `[(cocone A S).w]`.
-/
theorem ι_map {t u : Finset S} (h : t ⟶ u) (p : LaurentPolynomial (Algebra.adjoin A (t : Set S))) :
    laurentMap (Algebra.adjoin A (u : Set S)).val.toRingHom (((diag A S).map h).hom p) =
      ((cocone A S).ι.app t).hom p := by
  show ((diag A S).map h ≫ (cocone A S).ι.app u).hom p = _
  rw [(cocone A S).w]

/- English proof (translation)
Apply `AddMonoidAlgebra.coeff_injective` to reduce the goal to its premises. Use extensionality with `m`. Simplify using `only [laurentMap_coeff_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val, Subalgebra.coe_inclusion]`.
-/
theorem lm_val_incl {t u : Finset S} (h : (t : Set S) ⊆ u) (p : LaurentPolynomial (Algebra.adjoin A (t : Set S))) :
    laurentMap (Algebra.adjoin A (u : Set S)).val.toRingHom
        (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom p) =
      laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom p := by
  apply AddMonoidAlgebra.coeff_injective
  ext m
  simp only [laurentMap_coeff_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val,
    Subalgebra.coe_inclusion]

/- English proof (translation)
Proceed by induction on `x using LaurentPolynomial.induction_on' with`. Consider the case `add p r hp hr`. Take `⟨t, y, rfl⟩` from `hp`. Take `⟨t', y', rfl⟩` from `hr`. Establish `h1 : (t : Set S) ⊆ ((t ⊔ t' : Finset S) : Set S)` using `Finset.coe_subset.2 le_sup_left`.

Establish `h2 : (t' : Set S) ⊆ ((t ⊔ t' : Finset S) : Set S)` using `Finset.coe_subset.2 le_sup_right`. Use `⟨t ⊔ t', laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h1)).toRingHom y + laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h2)).toRingHom y', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, lm_val_incl A S h1, lm_val_incl A S h2]`. Consider the case `C_mul_T n a`. Establish `hmem : a ∈ Algebra.adjoin A (({a} : Finset S) : Set S)` using `Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self a))`.

Use `⟨{a}, LaurentPolynomial.C (⟨a, hmem⟩ : Algebra.adjoin A (({a} : Finset S) : Set S)) * LaurentPolynomial.T n, ?_⟩` and prove the remaining obligations. Rewrite using `[val_CT]`.
-/
theorem exists_finset_adjoin_laurent_preimage (x : LaurentPolynomial S) : ∃ (t : Finset S) (y : LaurentPolynomial (Algebra.adjoin A (t : Set S))),
    x = laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom y := by
  classical
  induction x using LaurentPolynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨t, y, rfl⟩ := hp
    obtain ⟨t', y', rfl⟩ := hr
    have h1 : (t : Set S) ⊆ ((t ⊔ t' : Finset S) : Set S) := Finset.coe_subset.2 le_sup_left
    have h2 : (t' : Set S) ⊆ ((t ⊔ t' : Finset S) : Set S) := Finset.coe_subset.2 le_sup_right
    refine ⟨t ⊔ t', laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h1)).toRingHom y +
      laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h2)).toRingHom y', ?_⟩
    rw [map_add, lm_val_incl A S h1, lm_val_incl A S h2]
  | C_mul_T n a =>
    have hmem : a ∈ Algebra.adjoin A (({a} : Finset S) : Set S) :=
      Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self a))
    refine ⟨{a}, LaurentPolynomial.C (⟨a, hmem⟩ : Algebra.adjoin A (({a} : Finset S) : Set S)) *
      LaurentPolynomial.T n, ?_⟩
    rw [val_CT]

/- English proof (translation)
Use `laurentMap_injective (Algebra.adjoin A ((i ⊔ j : Finset S) : Set S)).val.toRingHom Subtype.val_injective ?_` and prove the remaining obligations. Conclude with `(lm_val_incl A S (Finset.coe_subset.2 (le_sup_left : i ≤ i ⊔ j)) xi).trans (h.trans (lm_val_incl A S (Finset.coe_subset.2 (le_sup_right : j ≤ i ⊔ j)) xj).symm)`.
-/
theorem laurent_adjoin_eq_of_image_eq [DecidableEq S] {i j : Finset S} (xi : LaurentPolynomial (Algebra.adjoin A (i : Set S)))
    (xj : LaurentPolynomial (Algebra.adjoin A (j : Set S)))
    (h : laurentMap (Algebra.adjoin A (i : Set S)).val.toRingHom xi =
      laurentMap (Algebra.adjoin A (j : Set S)).val.toRingHom xj) :
    laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono
        (Finset.coe_subset.2 (le_sup_left : i ≤ i ⊔ j)))).toRingHom xi =
      laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono
        (Finset.coe_subset.2 (le_sup_right : j ≤ i ⊔ j)))).toRingHom xj := by
  refine laurentMap_injective (Algebra.adjoin A ((i ⊔ j : Finset S) : Set S)).val.toRingHom
    Subtype.val_injective ?_
  exact (lm_val_incl A S (Finset.coe_subset.2 (le_sup_left : i ≤ i ⊔ j)) xi).trans
    (h.trans (lm_val_incl A S (Finset.coe_subset.2 (le_sup_right : j ≤ i ⊔ j)) xj).symm)

def coconeIsColimit : IsColimit (cocone A S) := by
  classical
  haveI : ReflectsColimitsOfShape (Finset S) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (cocone A S)) ?_ ?_)
  · intro x
    exact exists_finset_adjoin_laurent_preimage A S x
  · intro i j xi xj h
    exact ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, laurent_adjoin_eq_of_image_eq A S xi xj h⟩

end GlobalTheory.EtC.GmStep.KillColim
end

namespace GlobalTheory.EtC.GmStep.KillColim

/- English proof (translation)
Rewrite using `[laurentMap_comp]`. Use `congr 1`.
-/
theorem val_laurent (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (t : Finset S) :
    (laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom).comp
        (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S)))) = laurentMap (algebraMap A S) := by
  rw [laurentMap_comp]
  congr 1

/- English proof (translation)
Rewrite using `[laurentMap_comp]`. Use `congr 1`.
-/
theorem incl_laurent (A S : Type) [CommRing A] [CommRing S] [Algebra A S] {t u : Finset S}
    (h : (t : Set S) ⊆ u) :
    (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (R := A) h)).toRingHom).comp
        (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S)))) =
      laurentMap (algebraMap A (Algebra.adjoin A (u : Set S))) := by
  rw [laurentMap_comp]
  congr 1

/- English proof (translation)
Introduce `q A S _ _ _ hq n i x hx`. Establish `hu : IsUnit (q : (diag A S).obj ∅)`. Use `hq.map ((LaurentPolynomial.C : Algebra.adjoin A ((∅ : Finset S) : Set S) →+* _).comp (algebraMap A _))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this`.

Establish `e1 : spMap ((cocone A S).ι.app ∅).hom ≫ spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S)))) = spMap (laurentMap (algebraMap A S))` using `(spMap_comp' _ (laurentMap (Algebra.adjoin A ((∅ : Finset S) : Set S)).val.toRingHom)).trans (congrArg spMap (val_laurent A S ∅))`. Establish `hy0 : pull _ (spMap ((cocone A S).ι.app ∅).hom) _ _ (pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S))))) _ _ x) = 0` using `(pull_comp _ _ _ _ _ x).symm.trans ((congrArg (fun g => pull _ g (tw q i) n x) e1).trans hx)`. Take `⟨k, f, hk⟩` from `(GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag A S) (cocone A S) (coconeIsColimit A S) n i).2 ∅ _ hu hy0`. Establish `e2 : spMap ((diag A S).map f).hom ≫ spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S)))) = spMap (laurentMap (algebraMap A (Algebra.adjoin A (k : Set S))))` using `(spMap_comp' _ (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (R := A) (Finset.coe_subset.2 f.le))).toRingHom)).trans (congrArg spMap (incl_laurent A S (Finset.coe_subset.2 f.le)))`. Conclude with `⟨k, (congrArg (fun g => pull _ g (tw q i) n x) e2).symm.trans ((pull_comp _ _ _ _ _ x).trans hk)⟩`.
-/
theorem kill_colim : ∀ (q : ℕ) (A S : Type) [CommRing A] [CommRing S] [Algebra A S], IsUnit (q : A) →
    ∀ (n i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) n i),
    pull _ (spMap (laurentMap (algebraMap A S))) _ _ x = 0 →
    ∃ t : Finset S, pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S))))) _ _ x = 0 := by
  intro q A S _ _ _ hq n i x hx
  classical
  have hu : IsUnit (q : (diag A S).obj ∅) := by
    have := hq.map ((LaurentPolynomial.C : Algebra.adjoin A ((∅ : Finset S) : Set S) →+* _).comp
      (algebraMap A _))
    rw [map_natCast] at this
    exact this
  have e1 : spMap ((cocone A S).ι.app ∅).hom ≫
      spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S)))) =
      spMap (laurentMap (algebraMap A S)) :=
    (spMap_comp' _ (laurentMap (Algebra.adjoin A ((∅ : Finset S) : Set S)).val.toRingHom)).trans
      (congrArg spMap (val_laurent A S ∅))
  have hy0 : pull _ (spMap ((cocone A S).ι.app ∅).hom) _ _
      (pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S))))) _ _ x) = 0 :=
    (pull_comp _ _ _ _ _ x).symm.trans ((congrArg (fun g => pull _ g (tw q i) n x) e1).trans hx)
  obtain ⟨k, f, hk⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag A S) (cocone A S) (coconeIsColimit A S) n i).2 ∅ _ hu hy0
  have e2 : spMap ((diag A S).map f).hom ≫
      spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S)))) =
      spMap (laurentMap (algebraMap A (Algebra.adjoin A (k : Set S)))) :=
    (spMap_comp' _ (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (R := A)
      (Finset.coe_subset.2 f.le))).toRingHom)).trans
      (congrArg spMap (incl_laurent A S (Finset.coe_subset.2 f.le)))
  exact ⟨k, (congrArg (fun g => pull _ g (tw q i) n x) e2).symm.trans ((pull_comp _ _ _ _ _ x).trans hk)⟩

end GlobalTheory.EtC.GmStep.KillColim
