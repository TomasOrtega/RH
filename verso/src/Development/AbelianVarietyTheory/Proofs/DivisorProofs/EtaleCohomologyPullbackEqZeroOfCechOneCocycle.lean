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
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem cechDiag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : cechDiag f ≫ cechAug f = sch.map f := by
  ext n : 1
  simp only [cechDiag, cechAug]
  erw [NatTrans.comp_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]
  rfl

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem isCls_zero_deg_one (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    IsCls (0 : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F) (0 : H R E F ((1 : ℕ) : ℤ)) := by
  refine ⟨0, ?_, ?_⟩ <;> simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem cechDiag_δ {Y X : Scheme.{0}} (f : Y ⟶ X) (i : Fin 3) :
    (cechDiag f).app (op ⦋2⦌) ≫ SimplicialObject.δ (cech f) i = (cechDiag f).app (op ⦋1⦌) := by
  rw [SimplicialObject.δ, ← NatTrans.naturality]
  simp [sch, disc]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
