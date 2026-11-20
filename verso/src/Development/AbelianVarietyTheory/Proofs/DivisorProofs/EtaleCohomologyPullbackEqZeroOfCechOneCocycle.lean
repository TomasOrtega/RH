import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

def cechDiag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (arrows := fun _ : Fin (n.unop.len + 1) => yoneda.map f) (yoneda.map f)
    (fun _ => 𝟙 (yoneda.obj Y)) (fun _ => Category.id_comp _)
  naturality m n g := by
    apply WidePullback.hom_ext
    · intro j
      simp only [cech, Arrow.cechNerve]
      erw [Category.assoc, Category.assoc, WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
      rfl
    · simp only [cech, Arrow.cechNerve]
      erw [Category.assoc, Category.assoc, WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]
      rfl

/- English proof (translation)
Use extensionality with `n : 1`. Simplify using `only [cechDiag, cechAug]`. Use `erw [NatTrans.comp_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]`. Both sides reduce to the same expression.
-/
theorem cechDiag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : cechDiag f ≫ cechAug f = sch.map f := by
  ext n : 1
  simp only [cechDiag, cechAug]
  erw [NatTrans.comp_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]
  rfl

/- English proof (translation)
Apply the tactic sequence `refine ⟨0, ?_, ?_⟩ <;> simp`.
-/
theorem isCls_zero_deg_one (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    IsCls (0 : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F) (0 : H R E F ((1 : ℕ) : ℤ)) := by
  refine ⟨0, ?_, ?_⟩ <;> simp

/- English proof (translation)
Rewrite using `[SimplicialObject.δ, ← NatTrans.naturality]`. Simplify using `[sch, disc]`.
-/
theorem cechDiag_δ {Y X : Scheme.{0}} (f : Y ⟶ X) (i : Fin 3) :
    (cechDiag f).app (op ⦋2⦌) ≫ SimplicialObject.δ (cech f) i = (cechDiag f).app (op ⦋1⦌) := by
  rw [SimplicialObject.δ, ← NatTrans.naturality]
  simp [sch, disc]

/- English proof (translation)
Establish `hc` using `congrArg (fun t => (free R).map ((cechDiag f).app (op ⦋2⦌)) ≫ t) hs`. Simplify using `only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul, ← Functor.map_comp_assoc, cechDiag_δ, comp_zero] at hc`. Establish `hc' : ((free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s : (free R).obj ((sch.obj Y).obj (op ⦋2⦌)) ⟶ F) = 0`. Simplify `hc` using `[Fin.sum_univ_succ]`. Establish `hd : (free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s = 0` using `hc'`.

Establish `key` using `(isCls_basic R F (cech f) 1).2.2.2.2 (sch.obj Y) (cechDiag f) s _ hx`. Rewrite `key` using `[hd]`. Establish `h0` using `(isCls_basic R F (sch.obj Y) 1).2.2.1 0 _ 0 key (isCls_zero_deg_one R F _)`. Rewrite using `[← cechDiag_aug f]`. Unfold `pull HK.pull HK.pre cpre at h0 ⊢`.

Use `Eq.trans ?_ h0` and prove the remaining obligations. Take `⟨z, rfl⟩` from `CohomologyClass.mk_surjective x`. Simplify using `only [CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]`. Unfold `zcomp`. Use `congr 1`.

Use `ext1`. Simplify using `[Functor.map_comp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]`.
-/
theorem pull_sch_eq_zero (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X)
    (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F) (hs : cobd s = 0) (x : H R (sch.obj X) F ((1 : ℕ) : ℤ))
    (hx : IsCls s (pull R (cechAug f) F ((1 : ℕ) : ℤ) x)) : pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  have hc := congrArg (fun t => (free R).map ((cechDiag f).app (op ⦋2⦌)) ≫ t) hs
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul, ← Functor.map_comp_assoc, cechDiag_δ,
    comp_zero] at hc
  have hc' : ((free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s : (free R).obj ((sch.obj Y).obj (op ⦋2⦌)) ⟶ F) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hd : (free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s = 0 := hc'
  have key := (isCls_basic R F (cech f) 1).2.2.2.2 (sch.obj Y) (cechDiag f) s _ hx
  rw [hd] at key
  have h0 := (isCls_basic R F (sch.obj Y) 1).2.2.1 0 _ 0 key (isCls_zero_deg_one R F _)
  rw [← cechDiag_aug f]
  unfold pull HK.pull HK.pre cpre at h0 ⊢
  refine Eq.trans ?_ h0
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  unfold zcomp
  congr 1
  ext1
  simp [Functor.map_comp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

end GlobalTheory.CechOne

end
